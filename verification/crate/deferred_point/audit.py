"""Check the two-entry point assembly in a linked executable."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from listing import ADD, DOUBLE, point_program
from crate.double4 import listing as double_reference, certificate as doubling
from crate.cached_add import listing as add_reference, certificate as addition
from evidence import write_evidence
from proof_build import compile_libraries, library_flags

HERE = Path(__file__).resolve().parent
FLAGS = ["-Q", "Point", "Ed25519Simd.Point", "-Q", "Double4", "Ed25519Simd.Double4",
         "-Q", "CachedAdd", "Ed25519Simd.CachedAdd", *library_flags()]


def compile_module(work, ns, name, source=None):
    dest = Path(ns) / (name + ".v")
    if source:
        shutil.copyfile(source / dest.name, work / dest)
    subprocess.run(["coqc", *FLAGS, str(dest)], cwd=work, check=True)


def audit(elf, work):
    compile_libraries(work)
    dest = work / "Point"
    dest.mkdir()
    for ns in ("Double4", "CachedAdd"):
        (work / ns).mkdir()
    for ns, folder, reference, modules in (
        ("Double4", "double4", double_reference, doubling.PROOF_MODULES),
        ("CachedAdd", "cached_add", add_reference, addition.PROOF_MODULES),
    ):
        reference.generate(work / ns)
        compile_module(work, ns, "Program")
        for name in modules[:modules.index("ReadFootprint") + 1]:
            compile_module(work, ns, name, HERE.parent / folder / "coq")
    symbols = point_program(elf, dest, DOUBLE, "Double")
    symbols.extend(point_program(elf, dest, ADD, "Add"))
    for name in ("DoubleBytes", "Double", "AddBytes", "Add"):
        compile_module(work, "Point", name)
    for name in ("DoublePath", "AddPath", "Outputs", "RawBounds", "Normalize", "Arithmetic", "Frame", "Concrete", "Audit", "Object"):
        compile_module(work, "Point", name, HERE / "coq")
    (dest / "Checked.v").write_text(
        "From Ed25519Simd.Point Require Audit Object.\n"
        "Definition checked : Audit.deferred_point_contract := Object.assembled_deferred_point_correct.\n"
        "Print Assumptions checked.\n")
    result = subprocess.check_output(["coqc", *FLAGS, "Point/Checked.v"], cwd=work, text=True)
    if result.strip() != "Closed under the global context":
        raise ValueError(result)
    (work / "assumptions.txt").write_text(result)
    command = ["coqchk", *FLAGS, "-silent", "Ed25519Simd.Point.Checked"]
    with (work / "coqchk.log").open("w") as log:
        subprocess.run(command, cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    checks = {"theorem": "Ed25519Simd.Point.Object.assembled_deferred_point_correct",
              "assumptions": result.strip(), "coqchk": {"command": command, "exit_code": 0}}
    write_evidence(elf, work, "deferred_point", checks, symbols,
                   [HERE.parents[1] / "mask_listing.py", *dict.fromkeys((*double_reference.SOURCES, *add_reference.SOURCES))], FLAGS)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
        audit(args.elf.resolve(), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="point-proof-") as work:
            audit(args.elf.resolve(), Path(work))
