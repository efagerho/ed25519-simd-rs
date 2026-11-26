"""Kernel-check deferred Dalek recompression against four symbols from one ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))

from crate.decompress_r import audit as decoder
from crate.small_order import audit as small_order
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence
from proof_build import ED25519_FLAGS, check_object, compile_signature_equations, component_flags, write_symbol_bytes

ENTRY = "ed25519_simd_dalek_recompress"
FLAGS = component_flags("dalek_recompress") + ED25519_FLAGS + [
    "-Q", "Decode", "Ed25519Simd.Decode", "-Q", "SmallOrder", "Ed25519Simd.SmallOrder"]
DALEK_MODULES = ("FieldOps", "Encoding", "Masks", "Batch", "Caller", "Schedule", "Audit", "Object")


def entry_bytes(elf, dest):
    address, size = symbol_extent(elf, ENTRY)
    raw = symbol_bytes(elf, address, size)
    path = dest / "ObjectBytes.v"
    write_symbol_bytes(path, raw)
    with path.open("a") as out:
        out.write(f"Definition address : Z := {address}.\n")
    return ENTRY, address, raw


def compile_modules(work, namespace, sources, modules):
    for name in modules:
        path = Path(namespace) / (name + ".v")
        source = sources / path.name
        if source.is_file():
            shutil.copyfile(source, work / path)
        subprocess.run(["coqc", *FLAGS, str(path)], cwd=work, check=True)


def replay(elf, work):
    work.mkdir(parents=True, exist_ok=False)
    for name in ("Dalek", "SmallOrder", "Decode"):
        (work / name).mkdir()
    entry = entry_bytes(elf, work / "Dalek")
    dec, helper = decoder.extract(elf, work / "Decode")
    small, _ = small_order.extract(elf, work / "SmallOrder")
    compile_signature_equations(work)
    compile_modules(work, "SmallOrder", small_order.HERE / "coq",
                    ("Program", "EntryBytes", "HelperBytes", *small_order.MODULES))
    compile_modules(work, "Decode", decoder.HERE / "coq",
                    ("Kernels", "Power", "Image", "Scale", "Unpack", "Decode", "Glue",
                     "Program", "DecoderBytes", "HelperBytes"))
    compile_modules(work, "Dalek", HERE / "coq", ("ObjectBytes", *DALEK_MODULES))
    checks = check_object(work, FLAGS, "dalek_recompress")
    asm = VERIFY.parent / "src/wide/avx512ifma"
    write_evidence(elf, work, "dalek_recompress", checks, [entry, dec, helper, small],
                   [asm / name for name in ("dalek_recompress.S", "decompress_r.S", "torsion.S",
                                             "point_encoding.inc", "pow22523.inc")], FLAGS)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    replay(args.elf.resolve(), args.output.resolve())
