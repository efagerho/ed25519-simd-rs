"""Check byte binding and observable failures for three linked wrapper mutations."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import HERE, WRAPPER
from elf import executable_offset, symbol_bytes, symbol_extent
from proof_build import component_flags, write_symbol_bytes
from scalar import listing


def run(elf, audit, work):
    for symbol, filename in ((WRAPPER, "symbol.bin"), (listing.SYMBOL, listing.SYMBOL + ".bin")):
        if symbol_bytes(elf, *symbol_extent(elf, symbol)) != (audit / filename).read_bytes():
            raise ValueError(f"release ELF differs from certified {symbol}")
    pc, size = symbol_extent(elf, WRAPPER)
    raw = symbol_bytes(elf, pc, size)
    for dep in ("arithmetic", "curve25519", "machine", "crate", "Scalar"):
        (work / dep).symlink_to(audit / dep)
    flags = component_flags("radix16") + ["-Q", "Scalar", "Ed25519Simd.Scalar"]
    dest = work / "Radix16"
    dest.mkdir()
    for obj in (audit / "Radix16").glob("*.vo"):
        (dest / obj.name).symlink_to(obj)
    # The shuffle context identifies the first pair, whose first store is at RDI.
    shift = bytes.fromhex("62 f1 cd 48 73 d0 34")
    shuffle = bytes.fromhex("62 f3 fd 48 43 d1 88 62 f3 fd 48 43 d9 dd 62 f1 fe 48 7f 17")
    mutations = [(shift, shift[:-1] + bytes([53])), (shuffle, shuffle[:6] + bytes([0x89]) + shuffle[7:])]
    if raw[:2] != b"\x57\xe8":
        raise ValueError("expected PUSH RDI and a rel32 call")
    mutations.append((raw[:6], raw[:2] + (int.from_bytes(raw[2:6], "little", signed=True) + 1)
                      .to_bytes(4, "little", signed=True)))
    for i, (old, new) in enumerate(mutations):
        if raw.count(old) != 1:
            raise ValueError("expected a unique mutation site")
        binary = work / "mutant.elf"
        shutil.copyfile(elf, binary)
        with binary.open("r+b") as file:
            offset = executable_offset(file, pc, size)
            file.seek(offset + raw.index(old))
            file.write(new)
        source = dest / "MutantBytes.v"
        write_symbol_bytes(source, symbol_bytes(binary, pc, size))
        with source.open("a") as file:
            file.write(f"Definition mutation := {i}%nat.\n")
        shutil.copyfile(HERE / "coq/Counterexample.v", dest / "Counterexample.v")
        for module in ("MutantBytes", "Counterexample"):
            subprocess.run(["coqc", *flags, f"Radix16/{module}.v"], cwd=work, check=True)
        print("Coq proved the", ("carry", "shuffle", "call target")[i], "mutation violates the public contract")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="radix16-mutations-") as tmp:
        run(args.elf.resolve(), args.audit.resolve(), Path(tmp))
