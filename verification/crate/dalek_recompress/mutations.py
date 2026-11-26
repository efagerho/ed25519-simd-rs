"""Replay the public Dalek theorem on independently modified copies of a release ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import ENTRY, FLAGS, decoder, entry_bytes
from elf import executable_offset, symbol_extent

# The original byte is checked before applying each single-byte edit.
CASES = (
    ("stack allocation", ENTRY, 0x1f, 0xc0, 0x80),
    ("canonical y comparison", ENTRY, 0x16b, 5, 6),
    ("preceding prefix address", ENTRY, 0x226, 0xc0, 0x80),
    ("inverse tail square count", ENTRY, 0x4ba, 5, 4),
    ("output byte placement", ENTRY, 0x606, 8, 7),
    ("small-order exclusion", ENTRY, 0x61d, 0x21, 0x09),
    ("canonical parity carry", ENTRY, 0x6b8, 51, 50),
    ("callee field carry", decoder.DECODER, 0xa84, 51, 50),
)


def check(elf, audit, work):
    for name in ("arithmetic", "machine", "curve25519", "ed25519", "crate", "SmallOrder"):
        (work / name).symlink_to(audit / name, target_is_directory=True)
    for name in ("Dalek", "Decode"):
        shutil.copytree(audit / name, work / name)

    def compile_file(path, **kwargs):
        return subprocess.run(["coqc", *FLAGS, path], cwd=work, **kwargs)

    compile_file("Dalek/Object.v", check=True)
    for label, symbol, offset, old, new in CASES:
        binary = work / "changed.elf"
        shutil.copyfile(elf, binary)
        pc, size = symbol_extent(elf, symbol)
        with binary.open("r+b") as stream:
            pos = executable_offset(stream, pc, size) + offset
            stream.seek(pos)
            if stream.read(1) != bytes([old]):
                raise ValueError(f"{label}: unexpected instruction at {symbol}+{offset:#x}")
            stream.seek(pos)
            stream.write(bytes([new]))
        entry_bytes(binary, work / "Dalek")
        compile_file("Dalek/ObjectBytes.v", check=True)
        if symbol == decoder.DECODER:
            decoder.extract(binary, work / "Decode")
            for name in ("Program", "DecoderBytes", "HelperBytes"):
                compile_file(f"Decode/{name}.v", check=True)
            # The newly lifted carry still binds to the new ELF. This case
            # must reach the arithmetic proof and compute the wrong residue.
            witness = work / "Dalek/Counterexample.v"
            witness.write_text("""From Coq Require Import ZArith.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require Import Program DecoderBytes HelperBytes.
From Ed25519Simd.Dalek Require Import FieldOps Audit.
Example bound_to_mutant : shared_image code DecoderBytes.address DecoderBytes.symbol_bytes
 HelperBytes.address HelperBytes.symbol_bytes.
Proof. vm_compute;repeat split;reflexivity. Qed.
Example wrong_difference : limbs(subtract_product code (fun _=>0) (fun _=>0) (fun _=>0)) mod prime <> 0.
Proof. vm_compute;discriminate. Qed.
""")
            compile_file("Dalek/Counterexample.v", check=True)
        result = compile_file("Dalek/Object.v", capture_output=True, text=True)
        if result.returncode == 0 or "Unable to unify" not in result.stderr:
            raise ValueError(f"unexpected public theorem outcome for {label}: {result.stderr[:600]}")
        print(f"Public recompression theorem rejected {label}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="dalek-mutations-") as temp:
        check(args.elf.resolve(), args.audit.resolve(), Path(temp))
