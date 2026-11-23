"""Rebind corrupted doubling instructions and check where Coq rejects them."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

POINT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(POINT))
from audit import FLAGS
from listing import DOUBLE, point_program
from elf import executable_offset, symbol_bytes, symbol_extent


def run_case(work, audit, binary, name, symbol, old, new, rejected_module):
    work.mkdir()
    dest = work / "Point"
    dest.mkdir()
    for dep in ("Double4", "CachedAdd", "machine", "arithmetic", "curve25519", "crate"):
        (work / dep).symlink_to(audit / dep)
    for dep in ("Add.vo", "AddBytes.vo"):
        (dest / dep).symlink_to(audit / "Point" / dep)

    image = bytearray(binary.read_bytes())
    pc, size = symbol_extent(binary, symbol)
    raw = symbol_bytes(binary, pc, size)
    if raw.count(old) != 1 or len(old) != len(new):
        raise ValueError(f"{name} needs one equal-length mutation site in {symbol}")
    with binary.open("rb") as source:
        offset = executable_offset(source, pc, size) + raw.index(old)
    image[offset:offset + len(old)] = new
    mutant = work / "mutant.elf"
    mutant.write_bytes(image)
    point_program(mutant, dest, DOUBLE, "Double")
    (dest / "Binding.v").write_text(
        "From Machine Require Import execution.Blocks.\n"
        "From Ed25519Simd.Point Require Double DoubleBytes.\n"
        "Example binds : image Double.program = DoubleBytes.symbol_bytes /\\ valid_program Double.program=true.\n"
        "Proof. split;vm_compute;reflexivity. Qed.\n")
    for module in ("DoubleBytes", "Double", "Binding", "DoublePath", "AddPath", "Outputs"):
        if module in ("DoublePath", "AddPath", "Outputs"):
            shutil.copyfile(POINT / "coq" / (module + ".v"), dest / (module + ".v"))
        result = subprocess.run(["coqc", *FLAGS, f"Point/{module}.v"], cwd=work,
                                capture_output=True, text=True)
        if result.returncode:
            if module != rejected_module or "Unable to unify" not in result.stderr:
                raise RuntimeError(result.stderr)
            print(f"{name} passed byte binding and was rejected in {module}.v", flush=True)
            return
    raise AssertionError(f"accepted {name}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads((args.audit / "manifest.json").read_text())
    if hashlib.sha256(args.elf.read_bytes()).hexdigest() != manifest["elf"]["sha256"]:
        parser.error("the audit must describe the supplied ELF")
    cases = (
        ("three-rounds", DOUBLE[0], "b907000000", "b906000000", "DoublePath"),
        ("defer-one-round-early", DOUBLE[1], "83f904", "83f905", "DoublePath"),
        ("low-half-instead-of-high", DOUBLE[1], "6272fd48b5e8", "6272fd48b4e8", "Outputs"),
    )
    with tempfile.TemporaryDirectory(prefix="point-mutations-") as directory:
        for name, sym, old, new, module in cases:
            run_case(Path(directory) / name, args.audit.resolve(), args.elf.resolve(), name, sym,
                     bytes.fromhex(old), bytes.fromhex(new), module)
