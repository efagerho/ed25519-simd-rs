"""Check semantic fault rejection, byte binding and a harmless-reordering control.

Run with Coq/LLVM/binutils on PATH. --native also requires AVX-512F/DQ/IFMA.
Each case gets a private source tree; the checkout is never mutated.
"""
import argparse
import ctypes
import difflib
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.append(str(ROOT / "verification"))
from proof_build import component_flags
from listing import SOURCES, SYMBOL
from generate_listing import assemble, assembly_source
from elf import symbol_bytes, symbol_extent

MUTATIONS = {
    "remove-input-reduction": ("    ca_reduce 0\n", "", False),
    "reuse-wrong-cached-operand": ("    ca_load r8, 320, 22", "    ca_load r8, 0, 22", False),
    "remove-top-carry-fold": ("    vpmadd52luq zmm12, zmm17, zmm28\n", "", False),
    "ignore-compute-t": ("    mov rcx, rdx\n", "    mov ecx, 0\n", False),
    "omit-x-stores": ("    ca_store rdi, 0, 0\n", "", False),
    "reorder-constant-loads": (
        "    mov eax, 19\n    vpbroadcastq zmm28, rax\n"
        "    mov rax, 0x7ffffffffffff\n    vpbroadcastq zmm29, rax\n",
        "    mov rax, 0x7ffffffffffff\n    vpbroadcastq zmm29, rax\n"
        "    mov eax, 19\n    vpbroadcastq zmm28, rax\n", True),
}


def native_check(binary):
    flags = Path("/proc/cpuinfo").read_text()
    if any(flag not in flags for flag in ("avx512f", "avx512dq", "avx512ifma")):
        raise ValueError("--native requires AVX-512F/DQ/IFMA")
    library = ctypes.CDLL(str(binary.resolve()))
    probe = library.probe
    probe.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_uint64, ctypes.c_uint64]
    probe.restype = None
    fixtures = json.loads((ROOT / "tests/vectors/cached_add.json").read_text())
    prime, radix = 2**255-19, 2**51

    def buffer():
        backing = ctypes.create_string_buffer(1280+63)
        return backing, (ctypes.c_uint64*160).from_address((ctypes.addressof(backing)+63) & ~63)

    for affine in (False, True):
        for full in (False, True):
            for first in range(len(fixtures)):
                p_backing, point = buffer()
                c_backing, cached = buffer()
                lanes = [fixtures[(first+j) % len(fixtures)] for j in range(8)]
                for c in range(4):
                    for i in range(5):
                        for j, case in enumerate(lanes):
                            point[40*c+8*i+j] = case["point"][c][i]
                            cached[40*c+8*i+j] = case["cached"][c][i]
                cache_before = list(cached)
                probe(point, cached, full, affine)
                if list(cached) != cache_before:
                    return {"failure": "cache modified", "affine": affine, "compute_t": full}
                for j, case in enumerate(lanes):
                    for c in range(4):
                        limbs = [point[40*c+8*i+j] for i in range(5)]
                        expected = (0 if c == 3 and not full else int.from_bytes(
                            bytes.fromhex(case["affine" if affine else "projective"][c]), "little"))
                        value = sum(n*radix**i for i, n in enumerate(limbs)) % prime
                        if (value != expected or any(n >= (2**52 if i == 1 else radix)
                                                    for i, n in enumerate(limbs)) or
                                (c == 3 and not full and any(limbs))):
                            return {"failure": "arithmetic/bounds", "case": case["name"],
                                    "affine": affine, "compute_t": full, "coordinate": c,
                                    "limbs": limbs, "value": value, "expected": expected}
    return {"passed": True, "lane_cases": 4*8*len(fixtures)}


def run_case(name, old, new, passes, output, native):
    work = output / name
    work.mkdir()
    repo = work / "repo"
    shutil.copytree(ROOT / "verification", repo / "verification",
                    ignore=shutil.ignore_patterns("__pycache__", "*.vo", "*.glob", "*.vok", "*.vos"))
    sources = [repo / src.relative_to(ROOT) for src in SOURCES]
    sources[0].parent.mkdir(parents=True)
    for src, dest in zip(SOURCES, sources):
        shutil.copyfile(src, dest)
    candidates = [src for src in sources if old in src.read_text()]
    if len(candidates) != 1:
        raise ValueError(f"ambiguous or missing mutation anchor: {name}")
    source, = candidates
    original = source.read_text()
    changed = original.replace(old, new, 1)
    source.write_text(changed)
    (work / "mutation.diff").write_text("".join(difflib.unified_diff(
        original.splitlines(True), changed.splitlines(True), fromfile=source.name, tofile=source.name)))
    assemble(assembly_source(work, sources), work, "assembly", SYMBOL)
    wrapper = work / "wrapper.c"
    wrapper.write_text(f"extern void {SYMBOL}(void*, const void*, unsigned long, unsigned long);\n"
                       f"void probe(void *p, const void *q, unsigned long t, unsigned long a) {{ {SYMBOL}(p,q,t,a); }}\n")
    binary = work / "code.so"
    subprocess.run(["cc", "-shared", "-fPIC", "-Wl,-z,noexecstack", wrapper,
                    work / "assembly.o", "-o", binary], check=True)
    audit = work / "audit"
    with (work / "audit.log").open("w") as log:
        status = subprocess.run([sys.executable, "-B", repo / "verification/crate/cached_add/audit.py",
                                 binary, "--output", audit], stdout=log, stderr=subprocess.STDOUT).returncode
    log = (work / "audit.log").read_text()
    if passes != (status == 0):
        raise ValueError(f"unexpected certificate result for {name}; see {work / 'audit.log'}")
    failure = None
    if not passes:
        match = re.search(r'File "\./([^\"]+\.v)", line (\d+)', log)
        if not match or match[1] not in {"Kernels.v", "Calls.v", "Logical.v", "Routing.v", "Arithmetic.v", "FrameProof.v"}:
            raise ValueError(f"not an arithmetic/control/memory proof rejection: {name}")
        failure = {"module": match[1], "line": int(match[2])}
    # Independently show every mutant remains a valid, accurately modeled symbol.
    # A parser error or byte mismatch is not counted as semantic fault detection.
    address, size = symbol_extent(binary, SYMBOL)
    raw = symbol_bytes(binary, address, size)
    (audit / "MutationBinding.v").write_text(
        "From Coq Require Import List ZArith.\nFrom Machine Require Import execution.Blocks.\n"
        "From Ed25519Simd.CachedAdd Require Import Program.\nImport ListNotations. Open Scope Z_scope.\n"
        "Example exact_bytes : image add_cached_program = [" + ";".join(map(str, raw)) +
        "].\nProof. vm_compute;reflexivity. Qed.\n"
        "Example valid_layout : valid_program add_cached_program=true.\nProof. vm_compute;reflexivity. Qed.\n")
    subprocess.run(["coqc", *component_flags("cached_add"), "MutationBinding.v"], cwd=audit, check=True)
    result = {"name": name, "certificate_passed": status == 0, "failure": failure,
              "byte_binding_passed": True, "symbol_sha256": hashlib.sha256(raw).hexdigest()}
    if native:
        result["native"] = native_check(binary)
        if passes != result["native"].get("passed", False):
            raise ValueError(f"native result disagrees with intended mutation: {name}")
    (work / "result.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"{name}: {'certificate passed' if passes else 'semantic proof rejected'}; byte binding passed", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new directory for retained evidence")
    parser.add_argument("--native", action="store_true", help="also check independent arithmetic fixtures on hardware")
    args = parser.parse_args()
    if (ROOT / "verification").resolve() in args.output.resolve().parents:
        parser.error("choose an output directory outside the verification source tree")
    args.output.mkdir(parents=True, exist_ok=False)
    results = [run_case(name, *mutation, args.output.resolve(), args.native)
               for name, mutation in MUTATIONS.items()]
    (args.output / "results.json").write_text(json.dumps(results, indent=2)+"\n")


if __name__ == "__main__":
    main()
