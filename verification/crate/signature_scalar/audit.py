"""Bind the pre-hash scalar check to its linked instructions and RIP-relative order."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence
from proof_build import check_object, compile_libraries, component_flags, write_symbol_bytes

SYMBOL = "ed25519_simd_prepare_signature_scalars"
MODULES = ("Program", "Audit", "Inputs", "Arithmetic", "Words", "Execution", "Object", "EntryTests")


def extract(binary, dest):
    pc, size = symbol_extent(binary, SYMBOL)
    raw = symbol_bytes(binary, pc, size)
    # objdump suggests the first constant address. Coq independently assembles
    # every RIP displacement and checks all 32 literal bytes against L.
    dump = subprocess.check_output(["objdump", "-d", "-Mintel", "--disassemble=" + SYMBOL, binary],
                                   text=True)
    location = re.search(r"\bvpcmp\w*\s+[^\n]*\[rip[^\]]*\]\s*#\s*([0-9a-f]+)", dump)
    if location is None:
        raise ValueError("missing RIP-relative order comparison")
    order = int(location[1], 16)
    literals = symbol_bytes(binary, order, 32, readonly_data=True)
    for module, addr, data in (("ObjectBytes", pc, raw), ("OrderBytes", order, literals)):
        path = dest / (module + ".v")
        write_symbol_bytes(path, data)
        with path.open("a") as f:
            f.write(f"Definition address : Z := {addr}.\n")
    return [(SYMBOL, pc, raw), ("scalar_order", order, literals)]


def audit(binary, work):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work)
    dest = work / "SignatureScalar"
    dest.mkdir()
    symbols = extract(binary, dest)
    flags = component_flags("signature_scalar")
    for name in ("ObjectBytes", "OrderBytes", *MODULES):
        path = dest / (name + ".v")
        if name in MODULES:
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *flags, path.relative_to(work)], cwd=work, check=True)
    checks = check_object(work, flags, "signature_scalar")
    write_evidence(binary, work, "signature_scalar", checks, symbols,
                   [VERIFY.parent / "src/scalar/radix16.S", HERE / "coq/Counterexample.v"], flags)
    print(f"Checked {checks['theorem']} in {binary}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    audit(args.elf.resolve(), args.output.resolve())
