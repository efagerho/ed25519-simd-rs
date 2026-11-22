"""Replay changes to the linked order, carry and invalid-lane selection."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import HERE, extract
from elf import load_offset
from proof_build import component_flags


def run(binary, audit, work):
    dest = work / "SignatureScalar"
    dest.mkdir()
    symbols = extract(binary, dest)
    for (_, _, data), path in zip(symbols, ("symbol.bin", "scalar_order.bin")):
        if data != (audit / path).read_bytes():
            raise ValueError(f"release ELF differs from certified {path}")
    for directory in ("arithmetic", "machine", "crate", "curve25519"):
        (work / directory).symlink_to(audit / directory)
    for path in (audit / dest.name).glob("*.vo"):
        (dest / path.name).symlink_to(path)
    shutil.copyfile(HERE / "coq/Counterexample.v", dest / "Counterexample.v")
    flags = component_flags("signature_scalar")
    variants = [
        ("accept S = L", 1, bytes.fromhex("ed d3 f5 5c"), bytes.fromhex("ee d3 f5 5c")),
        ("drop the first carry", 0, bytes.fromhex("62 f1 f5 4a d4 cd"), bytes.fromhex("62 f1 f5 4b d4 cd")),
        ("leak digits into a rejected lane", 0, bytes.fromhex("62 f2 dd 49 64 c0"), bytes.fromhex("62 f2 fd 49 64 c0")),
    ]
    for i, (name, index, old, new) in enumerate(variants):
        _, pc, raw = symbols[index]
        if raw.count(old) != 1:
            raise ValueError(f"expected a unique mutation site for {name}")
        damaged = work / "mutant.elf"
        shutil.copyfile(binary, damaged)
        with damaged.open("r+b") as f:
            pos = load_offset(f, pc, len(raw), readonly_data=bool(index))
            f.seek(pos + raw.index(old))
            f.write(new)
        extract(damaged, dest)
        (dest / "ObjectBytes.v").rename(dest / "MutantCode.v")
        (dest / "OrderBytes.v").rename(dest / "MutantOrder.v")
        with (dest / "MutantCode.v").open("a") as f:
            f.write(f"Definition mutation := {i}%nat.\n")
            difference = raw.index(old) + next(j for j, pair in enumerate(zip(old, new)) if pair[0] != pair[1])
            f.write(f"Definition changed_offset := {difference}%nat.\n")
        for module in ("MutantCode", "MutantOrder", "Counterexample"):
            subprocess.run(["coqc", *flags, dest.relative_to(work) / (module + ".v")], cwd=work, check=True)
        print("Coq rejected the mutation:", name)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="signature-scalar-mutations-") as tmp:
        run(args.elf.resolve(), args.audit.resolve(), Path(tmp))
