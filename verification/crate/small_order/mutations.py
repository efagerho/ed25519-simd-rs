"""Prove the negation of the public contract for four modified release ELFs."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import HERE, SYMBOLS, extract
from elf import executable_offset, symbol_bytes, symbol_extent
from proof_build import component_flags

# Change one weight, skip PUSH RBP, fold the Y carry with the wrong
# register, or drop the last exact root in the other linked symbol.
CASES = (
    ("weight", 0, "16 be 83 9f 00 49 06 57", "18 be 83 9f 00 49 06 57"),
    ("frame", 0, "75 06 31 c0", "75 07 31 c0"),
    ("carry", 0, "62 92 8d 48 b4 c4", "62 92 8d 48 b4 c5"),
    ("shared-mask", 1, "c5 e4 45 dc c5 f8 93 c3", "c5 e4 45 db c5 f8 93 c3"),
)


def run_case(elf, audit, work, case):
    name, index, before, after = case
    dest = work / "SmallOrder"
    dest.mkdir(parents=True)
    for dep in ("arithmetic", "curve25519", "machine", "crate"):
        (work / dep).symlink_to(audit / dep)

    pc, size = symbol_extent(elf, SYMBOLS[index][0])
    raw = symbol_bytes(elf, pc, size)
    before, after = bytes.fromhex(before), bytes.fromhex(after)
    if raw.count(before) != 1 or len(before) != len(after):
        raise ValueError(f"{name}: expected one fixed-width mutation site")
    binary = work / "mutant.elf"
    shutil.copyfile(elf, binary)
    with binary.open("r+b") as out:
        offset = executable_offset(out, pc, size)
        out.seek(offset + raw.index(before))
        out.write(after)
    extract(binary, dest)
    for dep in ("Program", "EntryBytes", "HelperBytes", "Audit", "Counterexample"):
        path = dest / (dep + ".v")
        if dep in ("Audit", "Counterexample"):
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *component_flags("small_order"), str(path.relative_to(work))],
                       cwd=work, check=True)
    print(f"{name}: Coq proved the mutated ELF violates small_order_contract", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    audit = args.audit.resolve()
    for (symbol, _), filename in zip(SYMBOLS, ("symbol.bin", SYMBOLS[1][0] + ".bin")):
        if symbol_bytes(args.elf, *symbol_extent(args.elf, symbol)) != (audit / filename).read_bytes():
            raise ValueError(f"release ELF differs from the certified {symbol}")
    with tempfile.TemporaryDirectory(prefix="small-order-mutations-") as tmp:
        for case in CASES:
            run_case(args.elf, audit, Path(tmp) / case[0], case)
