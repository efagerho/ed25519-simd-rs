"""Patch a release ELF and require rejection of the key-table theorem."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import ENTRY, FLAGS, build_project, decoder
from crate.post_hash.build import symbol_inputs
from crate.post_hash.check_mutations import compile_module, mutate
from elf import executable_offset, symbol_extent

# Equal-length replacements preserve symbol addresses and every other byte.
CASES = (
    ("stack allocation", ENTRY, "48 81 ec c0 03 00 00", "48 81 ec 80 03 00 00"),
    ("single-lane branch", ENTRY, "83 fb 01 0f 84 42 01", "83 fb 08 0f 84 42 01"),
    ("negative T mask", ENTRY, "b8 7c 00 00 00 c5 f8 92", "b8 78 00 00 00 c5 f8 92"),
    ("negative tail store", ENTRY, "62 53 fd 48 3b 56 04 00", "62 53 fd 48 3b 56 04 01"),
    ("eighth multiple", ENTRY, "41 83 ff 08 74", "41 83 ff 07 74"),
    ("affine operand", ENTRY, "00 b9 01 00 00 00 e8", "00 b9 00 00 00 00 e8"),
    ("shared carry shift", decoder.DECODER, "62 f1 ad 48 73 d0 33", "62 f1 ad 48 73 d0 32"),
)


def check(elf, audit, work):
    for name in ("arithmetic", "machine", "curve25519", "crate", "CachedAdd"):
        (work / name).symlink_to(audit / name, target_is_directory=True)
    for name in ("KeyTable", "Decode"):
        shutil.copytree(audit / name, work / name, ignore=shutil.ignore_patterns("Checked.*"))
    build_project(work)
    subprocess.run(["make", "-s", "KeyTable/Object.vo"], cwd=work, check=True)
    for label, symbol, old, new in CASES:
        # Reset the checked sources and objects together. Each mutant is compared
        # with the same positive control, including all interior instruction proofs.
        for name in ("KeyTable", "Decode"):
            shutil.copytree(audit / name, work / name, dirs_exist_ok=True, ignore=shutil.ignore_patterns("Checked.*"))
        changed = work / "changed.elf"
        if symbol == decoder.DECODER:
            # Select the carry helper by its audited entry offset. The same
            # shift encoding can occur in unrelated exponentiation blocks.
            shutil.copyfile(elf, changed)
            pc, size = symbol_extent(elf, symbol)
            with changed.open("r+b") as stream:
                pos = executable_offset(stream, pc, size) + 0xa7e
                stream.seek(pos)
                if stream.read(len(bytes.fromhex(old))) != bytes.fromhex(old):
                    raise ValueError("unexpected first carry instruction")
                stream.seek(pos)
                stream.write(bytes.fromhex(new))
            decoder.extract(changed, work / "Decode")
            for name in ("Program", "DecoderBytes", "HelperBytes"):
                compile_module(work, FLAGS, "Decode", name)
            witness = work / "KeyTable/Counterexample.v"
            witness.write_text("""From Coq Require Import ZArith.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require Import Program DecoderBytes HelperBytes.
From Ed25519Simd.KeyTable Require Import Fields Image.
Local Open Scope Z_scope.
Example mutant_still_bound : helper_image code DecoderBytes.address DecoderBytes.symbol_bytes
 HelperBytes.address HelperBytes.symbol_bytes.
Proof. vm_compute;repeat split;reflexivity. Qed.
Definition input (i:nat) := if Nat.eqb i 0 then 2^50 else 0.
Example wrong_coordinate : limbs(linear_result code Twice input input) mod prime <>
 (2*limbs input) mod prime.
Proof. vm_compute;discriminate. Qed.
""")
            compile_module(work, FLAGS, "KeyTable", "Counterexample")
        else:
            mutate(elf, changed, symbol, old, new)
        symbol_inputs(changed, work / "KeyTable", {"Object": ENTRY})
        result = subprocess.run(["make", "-s", "-j4", "KeyTable/Object.vo"], cwd=work,
                                capture_output=True, text=True)
        output = result.stdout + result.stderr
        if not result.returncode or "Error: Unable to unify" not in output or "inconsistent assumptions" in output:
            raise AssertionError(f"expected a proof failure for {label}: {output[-1800:]}")
        print(f"Public key-table theorem rejected {label}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="key-table-mutations-") as temp:
        check(args.elf.resolve(), args.audit.resolve(), Path(temp))
