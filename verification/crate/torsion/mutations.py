"""Reassemble changed instructions and check that the release proof rejects them."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import HERE, SOURCE, SYMBOL, assemble, component_flags, program
from elf import symbol_bytes, symbol_extent
from proof_build import write_symbol_bytes


CASES = (
    ("weaken-all-lanes-guard", "cmp eax, 255", "cmp eax, 254", "Schedule", "paths_checked"),
    ("add-instead-of-subtract", "vpsubq zmm10, zmm30, zmm10", "vpaddq zmm10, zmm30, zmm10",
     "Schedule", "scheduled_arithmetic"),
    ("discard-last-root", "korw k3, k3, k4\n    kmovw eax, k3",
     "korw k3, k3, k3\n    kmovw eax, k3", "Masks", "long_shapes"),
    ("overwrite-saved-frame", "sub rsp, 960", "sub rsp, 896", "Schedule", "paths_checked"),
)


def run_case(work, audit, case):
    name, before, after, module, lemma = case
    work.mkdir()
    for dep in ("arithmetic", "curve25519", "machine", "crate"):
        (work / dep).symlink_to(audit / dep)
    dest = work / "Torsion"
    dest.mkdir()
    source = SOURCE.read_text()
    if source.count(before) != 1:
        raise ValueError(f"{name}: expected one assembly mutation site")
    changed = work / "mutant.S"
    changed.write_text(source.replace(before, after))
    raw = assemble(changed, work, "mutant", SYMBOL)
    binary = work / "mutant.so"
    subprocess.run(["ld", "-shared", "-o", binary, work / "mutant.o"], check=True)
    if program(binary, dest) != raw:
        raise ValueError(f"{name}: linking changed the mutated instructions")
    write_symbol_bytes(dest / "ObjectBytes.v", raw)
    # The changed ELF must still have a valid Coq listing for its own bytes.
    (dest / "Binding.v").write_text(
        "From Machine Require Import execution.MaskTrace.\n"
        "From Ed25519Simd.Torsion Require Import Program ObjectBytes.\n"
        "Example bound : bytes code = symbol_bytes /\\ well_formed code = true.\n"
        "Proof. vm_compute; split; reflexivity. Qed.\n")
    command = ["coqc", *component_flags("torsion")]
    for dep in ("Program", "ObjectBytes", "Binding"):
        subprocess.run([*command, f"Torsion/{dep}.v"], cwd=work, check=True)
    for dep in ("Schedule", "Masks"):
        source = HERE / "coq" / (dep + ".v")
        shutil.copyfile(source, dest / source.name)
        result = subprocess.run([*command, f"Torsion/{dep}.v"], cwd=work, text=True, capture_output=True)
        if dep != module:
            result.check_returncode()
            continue
        # Check failure at the proof itself, not a missing import or a tactic
        # error elsewhere in the module.
        lines = source.read_text().splitlines()
        begin = next(i for i, line in enumerate(lines, 1) if line.startswith(f"Lemma {lemma} "))
        end = next(i for i, line in enumerate(lines[begin:], begin + 1) if "Qed." in line)
        rejected = "Unable to unify" in result.stderr or f"(in proof {lemma}): Attempt to save an incomplete proof" in result.stderr
        if result.returncode == 0 or not rejected or not any(
                f"line {i}," in result.stderr for i in range(begin, end + 1)):
            raise RuntimeError(f"{name}: expected rejection in {dep}.{lemma}\n{result.stderr[:2000]}")
        print(f"{name}: Coq rejected {dep}.{lemma}", flush=True)
        return


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args()
    audit = args.audit.resolve()
    raw = symbol_bytes(args.elf, *symbol_extent(args.elf, SYMBOL))
    if raw != (audit / "symbol.bin").read_bytes():
        raise ValueError("audit and release ELF disagree on the original symbol")
    with tempfile.TemporaryDirectory(prefix="torsion-mutations-") as work:
        for case in CASES:
            run_case(Path(work) / case[0], audit, case)


if __name__ == "__main__":
    main()
