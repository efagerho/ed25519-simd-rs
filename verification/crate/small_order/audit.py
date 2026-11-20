"""Certify the small-order entry and every instruction it reaches in the torsion symbol."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.append(str(VERIFY))
from evidence import write_evidence
from mask_listing import linked_program
from proof_build import MASK_PROJECTS, check_object, compile_libraries, component_flags, write_symbol_bytes

SYMBOLS = [("ed25519_simd_small_order_ifma", "code"), ("ed25519_simd_check_8_torsion_ifma", "helper")]
MODULES = ("Audit", "Schedule", "Filter", "Exact", "Object")


def extract(binary, dest):
    symbols = linked_program(binary, SYMBOLS, dest)
    for module, (_, pc, raw) in zip(("EntryBytes", "HelperBytes"), symbols):
        path = dest / (module + ".v")
        write_symbol_bytes(path, raw)
        with path.open("a") as output:
            output.write(f"Definition address : Z := {pc}.\n")
    return symbols


def replay(binary, work):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work, projects=MASK_PROJECTS)
    dest = work / "SmallOrder"
    dest.mkdir()
    symbols = extract(binary, dest)
    flags = component_flags("small_order")
    for module in ("Program", "EntryBytes", "HelperBytes", *MODULES):
        path = dest / (module + ".v")
        if module in MODULES:
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *flags, str(path.relative_to(work))], cwd=work, check=True)
    checks = check_object(work, flags, "small_order")
    write_evidence(binary, work, "small_order", checks, symbols,
                   [VERIFY.parent / "src/wide/avx512ifma/torsion.S", HERE / "coq/Counterexample.v"], flags)
    print(f"Checked {checks['theorem']} against {binary}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    replay(args.elf.resolve(), args.output.resolve())
