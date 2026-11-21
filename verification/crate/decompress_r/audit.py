"""Build the decoder certificate for a linked x86-64 ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
from elf import symbol_bytes, symbol_extent
from mask_listing import instructions, instruction
from evidence import write_evidence
from proof_build import (MASK_PROJECTS, check_object, compile_libraries, compile_object,
                         component_flags, write_symbol_bytes)


DECODER = "ed25519_simd_zip215_decode_r"
HELPER = "ed25519_simd_check_8_torsion_ifma"


def vector_block(rows, start, end):
    result = []
    pc = start
    while pc < end:
        pc, name, args = rows[pc]
        lifted = instruction(name, args)
        if not lifted.startswith("Vector "):
            raise ValueError(f"unexpected {name} in vector kernel")
        result.append(lifted.removeprefix("Vector "))
    if pc != end:
        raise ValueError("fragment ends inside an instruction")
    return "[" + ";\n".join(result) + "]"


def extract(binary, dest):
    symbols = []
    metadata = []
    for name, module in [(DECODER, "DecoderBytes"), (HELPER, "HelperBytes")]:
        pc, size = symbol_extent(binary, name)
        raw = symbol_bytes(binary, pc, size)
        path = dest / (module + ".v")
        write_symbol_bytes(path, raw)
        with path.open("a") as out:
            out.write(f"Definition address : Z := {pc}.\n")
        metadata.append((name, pc, raw))
        symbols.append((pc, instructions(binary, name)))
    decoder, helper = symbols
    fragments = [(helper, 0xb90, 0xbfc), (helper, 0xcb0, 0xddc),
                 (helper, 0xc01, 0xca3), (decoder, 0xa7e, 0xadd),
                 (decoder, 0x7b7, 0x7f0), (decoder, 0x59b, 0x7b1)]
    defs = []
    for (base, rows), start, end in fragments:
        defs.append(vector_block(rows, base + start, base + end))
    (dest / "Program.v").write_text(
        "From Coq Require Import List ZArith.\n"
        "From Machine Require Import isa.Instructions.\n"
        "From Ed25519Simd.Decode Require Import Kernels.\n"
        "Import ListNotations.\nDefinition code := Kernels\n" + "\n".join(defs) + ".\n")
    return metadata


def main():
    sys.path.insert(0, str(HERE.parent / "pow2"))
    from certify import PROOF_MODULES
    from generate_listing import generate, SOURCES

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    dest = work / "Decode"
    dest.mkdir()
    elf = args.elf.resolve()
    symbols = extract(elf, dest)
    pc, size = symbol_extent(elf, "ed25519_simd_pow2_ifma")
    power = symbol_bytes(elf, pc, size)
    symbols.append(("ed25519_simd_pow2_ifma", pc, power))
    with (dest / "DecoderBytes.v").open("a") as out:
        out.write(f"Definition pow_pc : Z := {pc}.\n")
    compile_libraries(work, projects=MASK_PROJECTS)
    pow_dir = work / "Pow2"
    pow_dir.mkdir()
    if generate(pow_dir) != power:
        raise ValueError("linked pow2 differs from its assembly listing")
    sources = HERE.parent / "pow2/coq"
    compile_object(power, pow_dir, [sources / (name + ".v") for name in PROOF_MODULES],
                   sources / "Object.v", component_flags("pow2", ".", Path("..")))
    flags = component_flags("decompress_r") + ["-Q", "Pow2", "Ed25519Simd.Pow2"]
    for name in ("Kernels", "Power", "Image", "Limbs", "Scale", "Unpack", "Decode", "Glue", "Caller", "Chunks",
                 "Program", "DecoderBytes", "HelperBytes", "Audit", "Object"):
        source = dest / (name + ".v")
        if not source.exists():
            shutil.copyfile(HERE / "coq" / source.name, source)
        subprocess.run(["coqc", *flags, str(source)], cwd=work, check=True)
    checks = check_object(work, flags, "decompress_r")
    asm = SOURCES[0].parent
    write_evidence(elf, work, "decompress_r", checks, symbols,
                   [asm / "decompress_r.S", asm / "point_encoding.inc", asm / "torsion.S", *SOURCES], flags)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    main()
