"""Change linked instructions, relift the kernels and check the public theorem rejects each ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import DECODER, HELPER, extract
from elf import executable_offset, symbol_extent
from proof_build import component_flags


# Symbol-relative byte offsets. Check the original byte before changing it.
CASES = (
    ("stack allocation", DECODER, 0x12, 0x80, 0x40),
    ("second mask placement", DECODER, 0xe0, 8, 7),
    ("transpose index", DECODER, 0xb40, 1, 0),
    ("single-chain squares", DECODER, 0x843, 2, 3),
    ("field carry shift", DECODER, 0xa84, 51, 50),
    ("canonical parity XOR", DECODER, 0x4d1, 0xe4, 0xe5),
    ("scaled denominator", HELPER, 0xe18, 0x42, 0x43),
)


def check(elf, audit, work):
    flags = component_flags("decompress_r") + ["-Q", "Pow2", "Ed25519Simd.Pow2"]
    # The release audit has already kernel-checked these objects. All generated
    # inputs and every module that imports them are rebuilt in the private copy.
    for name in ("arithmetic", "curve25519", "machine", "crate", "Pow2"):
        (work / name).symlink_to(audit / name, target_is_directory=True)
    dest = work / "Decode"
    shutil.copytree(audit / "Decode", dest)
    pow_pc, _ = symbol_extent(elf, "ed25519_simd_pow2_ifma")

    def replay(binary):
        extract(binary, dest)
        with (dest / "DecoderBytes.v").open("a") as out:
            out.write(f"Definition pow_pc : Z := {pow_pc}.\n")
        for module in ("Program", "DecoderBytes", "HelperBytes"):
            subprocess.run(["coqc", *flags, f"Decode/{module}.v"], cwd=work, check=True)
        return subprocess.run(["coqc", *flags, "Decode/Object.v"], cwd=work,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

    replay(elf).check_returncode()
    for label, name, offset, old, new in CASES:
        pc, size = symbol_extent(elf, name)
        binary = work / "mutant.elf"
        shutil.copyfile(elf, binary)
        with binary.open("r+b") as stream:
            pos = executable_offset(stream, pc, size) + offset
            stream.seek(pos)
            if stream.read(1) != bytes([old]):
                raise ValueError(f"{label}: mutation site differs from the certified instruction")
            stream.seek(pos)
            stream.write(bytes([new]))
        result = replay(binary)
        if result.returncode == 0 or "Unable to unify" not in result.stdout:
            raise ValueError(f"unexpected proof outcome for {label}: {result.stdout[:600]}")
        if label == "field carry shift":
            (dest / "Counterexample.v").write_text("""From Coq Require Import ZArith.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require Import Kernels Power Image Program DecoderBytes HelperBytes.
Local Open Scope Z_scope.
Example altered_image_matches :
 kernel_image code DecoderBytes.address DecoderBytes.symbol_bytes HelperBytes.address HelperBytes.symbol_bytes.
Proof. vm_compute;repeat split;reflexivity. Qed.
Example altered_zero_product :
 limbs (apply_kernel code Multiply (fun _=>0) (fun _=>0)) mod prime <> 0.
Proof. vm_compute;discriminate. Qed.
""")
            subprocess.run(["coqc", *flags, "Decode/Counterexample.v"], cwd=work, check=True)
            print("Coq re-encoded the changed carry and proved that zero times zero has nonzero residue.",
                  flush=True)
        print(f"Public decoder theorem rejected {label}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="decompress-r-mutations-") as tmp:
        check(args.elf.resolve(), args.audit.resolve(), Path(tmp))
