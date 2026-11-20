"""Replay the linked digest conversion and its scalar-reducer certificate."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CRATE = HERE.parent
VERIFY = CRATE.parent
sys.path[:0] = [str(VERIFY), str(CRATE)]
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence
from proof_build import (check_object, compile_libraries, compile_object,
                         component_flags, write_symbol_bytes)
from scalar import certificate, listing

WRAPPER = "ed25519_simd_digest_to_radix16"


def linked_inputs(elf, directory):
    symbols = []
    for symbol in (WRAPPER, listing.SYMBOL):
        pc, size = symbol_extent(elf, symbol)
        symbols.append((symbol, pc, symbol_bytes(elf, pc, size)))
    linked = directory / "LinkedBytes.v"
    write_symbol_bytes(linked, symbols[0][2])
    with linked.open("a") as source:
        for name, (_, pc, _) in zip(("wrapper_pc", "reducer_pc"), symbols):
            source.write(f"Definition {name} : Z := {pc}.\n")
    return symbols


def audit(elf, work):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work)
    dest = work / "Radix16"
    dest.mkdir()
    symbols = linked_inputs(elf, dest)
    callee = work / "Scalar"
    callee.mkdir()
    raw = symbols[1][2]
    if listing.generate(callee) != raw:
        raise ValueError("linked scalar reducer differs from assembled reduce.S")
    sources = [CRATE / "scalar/coq" / (name + ".v") for name in certificate.PROOF_MODULES]
    compile_object(raw, callee, sources, CRATE / "scalar/coq/Object.v",
                   component_flags("scalar", ".", Path("..")))
    flags = component_flags("radix16") + ["-Q", "Scalar", "Ed25519Simd.Scalar"]
    for module in ("LinkedBytes", "Program", "Packing", "Routing",
                   "Audit", "Execution", "Object", "EntryTests"):
        path = dest / (module + ".v")
        if module != "LinkedBytes":
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *flags, str(path.relative_to(work))], cwd=work, check=True)
    checks = check_object(work, flags, "radix16")
    write_evidence(elf, work, "radix16", checks, symbols,
                   [VERIFY.parent / "src/scalar/radix16.S", listing.SOURCE], flags)
    print("Checked the linked digest-to-radix16 conversion and reducer in", elf)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    audit(args.elf.resolve(), args.output.resolve())
