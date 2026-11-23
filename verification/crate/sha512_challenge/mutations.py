"""Prove the negation of the release contract for each changed ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import HERE, NAMESPACE, extract, flags, write_input
from elf import load_offset


def run(binary, audit, work):
    symbols = extract(binary)
    for (_, _, data), name in zip(symbols, ("symbol.bin", "sha512_literals.bin")):
        if data != (audit / name).read_bytes():
            raise ValueError(f"input ELF differs from certified {name}")
    # Anchor each text edit to an actual instruction in this image. The first
    # occurrence suffices for instructions repeated across the unrolled body.
    edits = [
        ("smaller stack frame", 0, "48 81 ec c0 02 00 00", 3),
        ("wrong rotation", 0, "62 b1 b5 40 72 c4 0e", 6),
        ("wrong choice truth table", 0, "62 23 d5 40 25 e6 ca", 6),
        ("swapped transpose selection", 0, "62 13 bd 40 43 c2 88", 6),
        ("different K-loop branch target", 0, "49 39 d2 0f 85", 5),
        ("different masked tail load", 0, "62 11 7f ca 6f 04 02", 3),
        ("different final store mask", 0, "62 61 fe 4c 7f 07", 3),
        ("wrong shuffle-mask byte", 1, "07 06 05 04", 0),
        ("wrong padding threshold", 1, "50 00 00 00 00 00 00 00", 0),
        ("wrong initial state", 1, "08 c9 bc f3 67 e6 09 6a", 4),
        ("wrong round constant", 1, "22 ae 28 d7 98 2f 8a 42", 4),
    ]
    for label, index, anchor, delta in edits:
        _, address, data = symbols[index]
        offset = data.index(bytes.fromhex(anchor)) + delta
        mutant = work / "mutant.elf"
        shutil.copyfile(binary, mutant)
        with mutant.open("r+b") as dest:
            start = load_offset(dest, address, len(data), readonly_data=bool(index))
            dest.seek(start + offset)
            dest.write(bytes([data[offset] ^ 1]))
        damaged = extract(mutant)
        for name, (_, pc, raw) in zip(("Code", "Literals"), damaged):
            write_input(work / (name + ".v"), pc, raw)
        field = "linked_literals" if index else "linked_text"
        (work / "Counterexample.v").write_text(f"""From Coq Require Import List ZArith.
From {NAMESPACE} Require Import Audit.
From Mutations Require Code Literals.
Theorem rejected : ~ sha512_contract Code.address Code.symbol_bytes Literals.address Literals.symbol_bytes.
Proof.
  intro C. pose proof ({field} _ _ _ _ C) as E.
  apply (f_equal (fun xs=>nth {offset}%nat xs 0%Z)) in E.
  vm_compute in E; discriminate.
Qed.
""")
        for name in ("Code", "Literals", "Counterexample"):
            subprocess.run(["coqc", *flags(audit), "-Q", ".", "Mutations", name + ".v"],
                           cwd=work, check=True)
        if label == "wrong rotation":
            shutil.copyfile(HERE / "coq/RotationMutant.v", work / "RotationMutant.v")
            subprocess.run(["coqc", *flags(audit), "-Q", ".", "Mutations", "RotationMutant.v"],
                           cwd=work, check=True)
        print(f"Proved the public contract false for {label}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="sha512-mutations-") as tmp:
        run(args.elf.resolve(), args.audit.resolve(), Path(tmp))
