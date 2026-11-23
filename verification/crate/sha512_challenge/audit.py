"""Certify the eight-lane SHA-512 routine and its read-only data in a linked ELF."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence
from proof_build import SHARED_ENV, check_object, compile_libraries, stage_sources, write_project, write_symbol_bytes
from probes import check_hardware

SYMBOL = "ed25519_simd_sha512_challenge"
COMPONENT = "sha512_challenge"
NAMESPACE = "Ed25519Simd.Sha512Challenge"
MODULES = ("Compression", "Output", "Rounds", "Block", "Transpose", "Loader",
           "Probe", "Lanes", "Image", "Control", "Frame", "Rows", "Execution", "Refinement", "Audit", "Object")


def flags(root):
    return ["-Q", str(root / "sha512"), "SHA512",
            "-Q", str(root / "machine"), "Machine",
            "-Q", str(root / "Sha512Challenge"), NAMESPACE]


def extract(binary):
    pc, size = symbol_extent(binary, SYMBOL)
    raw = symbol_bytes(binary, pc, size)
    # The first RIP-relative VPADDQ broadcasts the prefix length at mask + 64.
    # Coq recomputes every relocation from this candidate and the symbol PC.
    prefix = bytes.fromhex("62 61 bd 50 d4 0d")
    if raw.count(prefix) != 1:
        raise ValueError("expected exactly one RIP-relative prefix-length broadcast")
    disp = raw.index(prefix) + len(prefix)
    ro = pc + disp + 4 + int.from_bytes(raw[disp:disp+4], "little", signed=True) - 64
    return [(SYMBOL, pc, raw), ("sha512_literals", ro, symbol_bytes(binary, ro, 832, readonly_data=True))]


def write_input(path, address, data):
    write_symbol_bytes(path, data)
    with path.open("a") as dest:
        dest.write(f"Definition address : Z := {address}.\n")


def audit(binary, work, native):
    work.mkdir(parents=True, exist_ok=False)
    symbols = extract(binary)
    if os.environ.get(SHARED_ENV):
        compile_libraries(work, projects=("machine",))
    else:
        stage_sources(VERIFY, work, ("machine",))
    stage_sources(VERIFY, work, ("sha512",))
    dest = work / "Sha512Challenge"
    dest.mkdir()
    for name, (_, address, data) in zip(("ObjectBytes", "LiteralBytes"), symbols):
        write_input(dest / (name + ".v"), address, data)
    for name in MODULES:
        shutil.copyfile(HERE / "coq" / (name + ".v"), dest / (name + ".v"))
    load_path = flags(Path("."))
    write_project(work, load_path, sorted(work.rglob("*.v")))
    subprocess.run(["coq_makefile", "-f", "_CoqProject", "-o", "Makefile"], cwd=work, check=True)
    subprocess.run(["make", "-s", "Sha512Challenge/Object.vo", "sha512/Vectors.vo",
                    "Sha512Challenge/Probe.vo"], cwd=work, check=True)
    checks = check_object(work, load_path, COMPONENT)
    if native:
        check_hardware(work, load_path, NAMESPACE)
    sources = [VERIFY.parent / "src/sha512.S", HERE / "probes.S", HERE / "coq/RotationMutant.v"]
    write_evidence(binary, work, COMPONENT, checks, symbols, sources, load_path)
    print(f"Checked {checks['theorem']} in {binary}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--native", action="store_true", help="check the Coq probe against AVX-512 hardware")
    args = parser.parse_args()
    audit(args.elf.resolve(), args.output.resolve(), args.native)
