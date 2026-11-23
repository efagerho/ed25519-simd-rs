"""Replay the deferred-carry point, ladder-step or full-ladder certificate from a linked ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from listing import ADD, DOUBLE, point_program
from crate.double4 import listing as double_reference, certificate as doubling
from crate.cached_add import listing as add_reference, certificate as addition
from crate.ladder_step import audit as ladder
from crate.full_ladder import audit as product
from evidence import write_evidence
from proof_build import GROUP_PROJECTS, check_object, compile_libraries, library_flags, write_symbol_bytes

HERE = Path(__file__).resolve().parent
FLAGS = ["-Q", "Point", "Ed25519Simd.Point", "-Q", "Double4", "Ed25519Simd.Double4",
         "-Q", "CachedAdd", "Ed25519Simd.CachedAdd", *library_flags()]


def compile_module(work, ns, name, source=None):
    dest = Path(ns) / (name + ".v")
    if source:
        shutil.copyfile(source / dest.name, work / dest)
    subprocess.run(["coqc", *FLAGS, str(dest)], cwd=work, check=True)


def compile_points(elf, work):
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
    return symbols


def compile_step(elf, work):
    pc, raw = ladder.read_symbol(elf, "ladder_step")
    dest = work / "LadderStep"
    dest.mkdir()
    linked = dest / "LinkedBytes.v"
    write_symbol_bytes(linked, raw)
    with linked.open("a") as out:
        out.write("From Ed25519Simd.Point Require DoubleBytes AddBytes.\n"
                  f"Definition wrapper_pc := {pc}%Z.\n"
                  "Definition double4_pc := DoubleBytes.private_pc.\n"
                  "Definition cached_pc := AddBytes.private_pc.\n")
    flags = [*FLAGS, "-Q", "LadderStep", "Ed25519Simd.LadderStep"]
    for name in (*ladder.MODULES, "EntryTests"):
        if name != "LinkedBytes":
            source = {"PointMode": HERE / "coq/PointMode.v",
                      "Callees": HERE / "coq/StepCallees.v"}.get(name, ladder.HERE / "coq" / (name + ".v"))
            shutil.copyfile(source, dest / (name + ".v"))
        subprocess.run(["coqc", *flags, "LadderStep/" + name + ".v"], cwd=work, check=True)
    return flags, ("ed25519_simd_ladder_step_ifma", pc, raw)


def audit(elf, work, component):
    compile_libraries(work, GROUP_PROJECTS)
    symbols = compile_points(elf, work)
    flags = FLAGS
    if component in ("ladder_step", "full_ladder"):
        flags, step = compile_step(elf, work)
        symbols.insert(0, step)
    if component == "full_ladder":
        flags, full = product.compile_full(elf, work, flags)
        symbols[:0] = full
    checks = check_object(work, flags, component)
    assembly = double_reference.SOURCE.parent
    sources = dict.fromkeys((*double_reference.SOURCES, *add_reference.SOURCES,
                             assembly / "ladder_step.S", product.SOURCE, product.STAGE_SOURCE,
                             HERE.parents[1] / "mask_listing.py", HERE / "tests/fixture.py",
                             HERE / "tests/private-entries.patch"))
    write_evidence(elf, work, "deferred_point", checks, symbols, sources, flags)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--component", choices=("deferred_point", "ladder_step", "full_ladder"), default="full_ladder")
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
        audit(args.elf.resolve(), args.output.resolve(), args.component)
    else:
        with tempfile.TemporaryDirectory(prefix="point-proof-") as work:
            audit(args.elf.resolve(), Path(work), args.component)
