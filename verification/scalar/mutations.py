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

from listing import SOURCE, SYMBOL
from generate_listing import assemble
from coq_proof import symbol_bytes
from elf import symbol_extent

ROOT = Path(__file__).resolve().parents[2]
MUTATIONS = {
    "remove-carry-rounding": (r"    sr_rrr vpaddq, 24, \i, 26" + "\n", "", False),
    "omit-modulus-product": (r"    sr_mod_product \i, 4, 27" + "\n", "", False),
    "wrong-montgomery-inverse": ("0x51da312547e1b", "0x51da312547e1c", False),
    "wrong-unpack-shift": (r"%(64-12*\i)", r"%(63-12*\i)", False),
    "omit-canonical-subtraction": ("    vpsubq zmm5, zmm0, zmm28\n", "    vmovdqa64 zmm5, zmm0\n", False),
    "omit-output-stores": (r"    vmovdqu64 [rdi + 64*\i], zmm\i" + "\n", "", False),
    "reorder-independent-clears": (
        ".irp i,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17",
        ".irp i,1,0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17", True),
}


def native_check(binary):
    import random
    flags = Path("/proc/cpuinfo").read_text()
    if any(flag not in flags for flag in ("avx512f", "avx512dq", "avx512ifma")):
        raise ValueError("--native requires AVX-512F/DQ/IFMA")
    library = ctypes.CDLL(str(binary.resolve()))
    probe = library.probe
    probe.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    probe.restype = None
    modulus, radix = 2**252+27742317777372353535851937790883648493, 2**52
    cases = [0, 1, modulus-1, modulus, modulus+1, 2*modulus-1, 2*modulus, 2**512-1]
    cases += [1 << i for i in range(512)]
    cases += [(modulus << i)+delta for i in range(260) for delta in (-1, 0, 1)
              if 0 <= (modulus << i)+delta < 2**512]
    rng = random.Random(42)
    cases += [rng.getrandbits(512) for _ in range(1024)]
    for first in range(0, len(cases), 8):
        lanes = (cases[first:first+8]+[0]*8)[:8]
        source = (ctypes.c_uint64*64)(*[h >> (64*i) & (2**64-1) for i in range(8) for h in lanes])
        output = (ctypes.c_uint64*40)(*([0xa5a5a5a5a5a5a5a5]*40))
        before = list(source)
        probe(output, source)
        if list(source) != before:
            return {"failure": "input modified", "input": lanes}
        for j, h in enumerate(lanes):
            limbs = [output[8*i+j] for i in range(5)]
            value = sum(n*radix**i for i, n in enumerate(limbs))
            if value != h % modulus or any(n >= radix for n in limbs):
                return {"failure": "canonical reduction", "input": str(h), "limbs": limbs,
                        "actual": str(value), "expected": str(h % modulus)}
    return {"passed": True, "lane_cases": len(cases)}


def run_case(name, old, new, passes, output, native):
    work = output / name
    work.mkdir()
    repo = work / "repo"
    shutil.copytree(ROOT / "verification", repo / "verification",
                    ignore=shutil.ignore_patterns("__pycache__", "*.vo", "*.glob", "*.vok", "*.vos"))
    source = repo / SOURCE.relative_to(ROOT)
    source.parent.mkdir(parents=True)
    original = SOURCE.read_text()
    if old not in original:
        raise ValueError(f"mutation anchor disappeared: {name}")
    changed = original.replace(old, new, 1)
    source.write_text(changed)
    (work / "mutation.diff").write_text("".join(difflib.unified_diff(
        original.splitlines(True), changed.splitlines(True), fromfile="original.S", tofile="mutated.S")))
    assemble(source, work, "assembly", SYMBOL)
    wrapper = work / "wrapper.c"
    wrapper.write_text(f"extern void {SYMBOL}(void*, const void*);\n"
                       f"void probe(void *p, const void *q) {{ {SYMBOL}(p,q); }}\n")
    binary = work / "code.so"
    subprocess.run(["cc", "-shared", "-fPIC", "-Wl,-z,noexecstack", wrapper,
                    work / "assembly.o", "-o", binary], check=True)
    audit = work / "audit"
    with (work / "audit.log").open("w") as log:
        status = subprocess.run([sys.executable, "-B", repo / "verification/scalar/audit.py",
                                 binary, "--output", audit], stdout=log, stderr=subprocess.STDOUT).returncode
    log = (work / "audit.log").read_text()
    if passes != (status == 0):
        raise ValueError(f"unexpected certificate result for {name}; see {work / 'audit.log'}")
    failure = None
    if not passes:
        match = re.search(r'File "\./([^\"]+\.v)", line (\d+)', log)
        if not match or match[1] not in {"Unpack.v", "Product.v", "Reduction.v", "Montgomery.v", "Finish.v", "Routing.v", "Logical.v", "FrameProof.v"}:
            raise ValueError(f"not an arithmetic/control/memory proof rejection: {name}")
        failure = {"module": match[1], "line": int(match[2])}
    # Independently show every mutant remains a valid, accurately modeled symbol.
    # A parser error or byte mismatch is not counted as semantic fault detection.
    address, size = symbol_extent(binary, SYMBOL)
    raw = symbol_bytes(binary, address, size)
    (audit / "MutationBinding.v").write_text(
        "From Coq Require Import List ZArith.\nFrom Machine Require Import Blocks.\n"
        "Require Import Program.\nImport ListNotations. Open Scope Z_scope.\n"
        "Example exact_bytes : image scalar_program = [" + ";".join(map(str, raw)) +
        "].\nProof. vm_compute;reflexivity. Qed.\n"
        "Example valid_layout : valid_program scalar_program=true.\nProof. vm_compute;reflexivity. Qed.\n")
    subprocess.run(["coqc", "-Q", "machine", "Machine", "MutationBinding.v"], cwd=audit, check=True)
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
