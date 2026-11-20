"""Kernel-check the ladder and its two callees from one linked ELF."""
import argparse
from importlib import import_module
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parent
sys.path.insert(0, str(VERIFY / "pow2"))
sys.path.insert(0, str(VERIFY))
from coq_proof import symbol_bytes
from elf import symbol_extent
from proof_build import (LOAD_PATH, check_object, compile_library, compile_machine,
                         compile_object, write_symbol_bytes)

CALLEES = [("double4", "double4", "Double4"), ("cached_add", "add_cached", "CachedAdd")]
MODULES = ["LinkedBytes", "Callees", "Schedule", "Audit", "Calls", "Execution", "Object"]


def read_symbol(elf, name):
    address, size = symbol_extent(elf, f"ed25519_simd_{name}_ifma")
    return address, symbol_bytes(elf, address, size)


def audit(elf, work):
    wrapper_pc, wrapper = read_symbol(elf, "ladder_step")
    callees = {symbol: read_symbol(elf, symbol) for _, symbol, _ in CALLEES}
    work.mkdir(parents=True, exist_ok=False)
    compile_machine(work / "machine")
    compile_library(VERIFY / "arithmetic", work / "arithmetic", "ProofArithmetic",
                    ("-Q", "../machine", "Machine"))
    flags = list(LOAD_PATH)
    for name, symbol, namespace in CALLEES:
        dest = work / namespace
        dest.mkdir()
        raw = callees[symbol][1]
        if import_module(f"{name}.listing").generate(dest) != raw:
            raise ValueError(f"linked {symbol} differs from the assembled source")
        sources = import_module(f"{name}.certificate").proof_sources()
        # Each callee imports modules named Program, Audit and Object.
        callee_flags = ["-R", ".", namespace, "-Q", "../machine", "Machine",
                        "-Q", "../arithmetic", "ProofArithmetic"]
        compile_object(raw, dest, sources, VERIFY / name / "coq/Object.v", callee_flags)
        flags.extend(["-Q", namespace, namespace])

    linked = work / "LinkedBytes.v"
    write_symbol_bytes(linked, wrapper)
    with linked.open("a") as f:
        for name, address in [("wrapper", wrapper_pc), ("double4", callees["double4"][0]),
                              ("cached", callees["add_cached"][0])]:
            f.write(f"Definition {name}_pc : Z := {address}.\n")
    for src in HERE.glob("coq/*.v"):
        shutil.copy(src, work)
    for module in MODULES[:-1]:
        subprocess.run(["coqc", *flags, module + ".v"], cwd=work, check=True)
    assumptions = subprocess.check_output(["coqc", *flags, "Object.v"], cwd=work, text=True)
    subprocess.run(["coqc", *flags, "EntryTests.v"], cwd=work, check=True)
    check_object(work, flags, assumptions)
    print("Checked Object.assembled_ladder_step_correct against", elf)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    audit(args.elf.resolve(), args.output.resolve())
