"""Kernel-check the ladder and its two callees from one linked ELF."""
import argparse
from importlib import import_module
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CRATE = HERE.parent
VERIFY = CRATE.parent
sys.path.insert(0, str(CRATE / "pow2"))
sys.path.insert(0, str(VERIFY))
sys.path.insert(0, str(CRATE))
from evidence import write_evidence
from elf import symbol_bytes, symbol_extent
from proof_build import (GROUP_PROJECTS, check_object, compile_libraries, component_flags,
                         compile_object, write_symbol_bytes)

CALLEES = [("double4", "double4", "Double4"), ("cached_add", "add_cached", "CachedAdd")]
MODULES = ["LinkedBytes", "PointMode", "Modes", "Callees", "PointTrace", "Schedule", "Audit", "Calls", "LeafHistory", "Execution", "History", "Object"]


def read_symbol(elf, name):
    address, size = symbol_extent(elf, f"ed25519_simd_{name}_ifma")
    return address, symbol_bytes(elf, address, size)


def compile_ladder(elf, work):
    wrapper_pc, wrapper = read_symbol(elf, "ladder_step")
    callees = {symbol: read_symbol(elf, symbol) for _, symbol, _ in CALLEES}
    flags = component_flags("ladder_step")
    for name, symbol, namespace in CALLEES:
        dest = work / namespace
        dest.mkdir()
        raw = callees[symbol][1]
        if import_module(f"{name}.listing").generate(dest) != raw:
            raise ValueError(f"linked {symbol} differs from the assembled source")
        sources = import_module(f"{name}.certificate").proof_sources()
        # Each callee imports modules named Program, Audit and Object.
        callee_flags = component_flags(name, ".", Path(".."))
        compile_object(raw, dest, sources, CRATE / name / "coq/Object.v", callee_flags)
        flags.extend(["-Q", namespace, "Ed25519Simd." + namespace])

    ladder = work / "LadderStep"
    ladder.mkdir()
    linked = ladder / "LinkedBytes.v"
    write_symbol_bytes(linked, wrapper)
    with linked.open("a") as f:
        for name, address in [("wrapper", wrapper_pc), ("double4", callees["double4"][0]),
                              ("cached", callees["add_cached"][0])]:
            f.write(f"Definition {name}_pc : Z := {address}.\n")
    for src in HERE.glob("coq/*.v"):
        shutil.copy(src, ladder)
    for module in MODULES[:-1]:
        subprocess.run(["coqc", *flags, "LadderStep/" + module + ".v"], cwd=work, check=True)
    subprocess.run(["coqc", *flags, "LadderStep/Object.v"], cwd=work, check=True)
    subprocess.run(["coqc", *flags, "LadderStep/EntryTests.v"], cwd=work, check=True)
    symbols = [("ed25519_simd_ladder_step_ifma", wrapper_pc, wrapper)]
    sources = [VERIFY.parent / "src/wide/avx512ifma/ladder_step.S"]
    for name, symbol, _ in CALLEES:
        symbols.append((f"ed25519_simd_{symbol}_ifma", *callees[symbol]))
        sources.extend(src for src in import_module(f"{name}.listing").SOURCES if src not in sources)
    return flags, symbols, sources


def audit(elf, work):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work, projects=GROUP_PROJECTS)
    flags, symbols, sources = compile_ladder(elf, work)
    checks = check_object(work, flags, "ladder_step")
    write_evidence(elf, work, "ladder_step", checks, symbols, sources, flags)
    print("Checked Ed25519Simd.LadderStep.Object.assembled_ladder_step_correct against", elf)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    audit(args.elf.resolve(), args.output.resolve())
