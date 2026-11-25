"""Kernel-check the eight-lane torsion result against a linked ELF symbol."""
import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from listing import SYMBOL, program
from elf import symbol_extent
from evidence import write_evidence
from proof_build import MASK_PROJECTS, certify_modules, component_flags

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parent / "pow2"))
from generate_listing import assemble

SOURCE = HERE.parents[2] / "src/wide/avx512ifma/torsion.S"
MODULES = ("Schedule", "Masks", "Audit", "Native", "Lane")


def matches_source(raw, work):
    # Rust LLVM and llvm-mc can choose different NOP sequences for .p2align.
    # Label the ends of each directive to compare every other byte exactly.
    lines = []
    count = 0
    for line in SOURCE.read_text().splitlines():
        if re.fullmatch(r"\.p2align [0-9]+", line.strip()):
            lines.extend([f"torsion_padding_{count}_begin:", line, f"torsion_padding_{count}_end:"])
            count += 1
        else:
            lines.append(line)
    marked = work / "marked.S"
    marked.write_text("\n".join(lines) + "\n")
    assembled = assemble(marked, work, "torsion", SYMBOL)
    if len(assembled) != len(raw):
        return False
    labels = subprocess.check_output(["nm", "-an", work / "torsion.o"], text=True)
    offsets = {name: int(addr, 16) for addr, name in
               re.findall(r"^([0-9a-f]+) t (torsion_padding_\w+)$", labels, re.M)}
    expected = bytearray(assembled)
    for i in range(count):
        lo, hi = (offsets[f"torsion_padding_{i}_{end}"] for end in ("begin", "end"))
        expected[lo:hi] = raw[lo:hi]
    return expected == raw


def replay(binary, work):
    raw = program(binary, work)
    with tempfile.TemporaryDirectory(dir=work) as temp:
        if not matches_source(raw, Path(temp)):
            raise ValueError("linked torsion symbol differs from the assembled source")
    checks = certify_modules(raw, work, [HERE / "coq" / (m + ".v") for m in MODULES],
                             HERE / "coq/Object.v", projects=MASK_PROJECTS)
    addr, _ = symbol_extent(binary, SYMBOL)
    write_evidence(binary, work, "torsion", checks, [(SYMBOL, addr, raw)], [SOURCE],
                   component_flags("torsion"))
    print(f"Checked {checks['theorem']} against {binary}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, help="retain the proof and manifest in a new directory")
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
        replay(args.elf, args.output)
    else:
        with tempfile.TemporaryDirectory(prefix="torsion-audit-") as work:
            replay(args.elf, Path(work))
