"""Check that three changed release symbols violate the staging theorem on an admissible call."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import HERE, SOURCE, SYMBOL
from elf import executable_offset, symbol_bytes, symbol_extent
from proof_build import component_flags, write_symbol_bytes

# Mutate the assembly macro and its typed listing together.
MUTANTS = (
    ("key index", "xor eax, 7", "xor eax, 6", "XorEax 7", "XorEax 6"),
    ("transpose", r"vpunpcklqdq zmm24, \a, \b", r"vpunpckhqdq zmm24, \a, \b",
     "UnpackQ false 24 r (r+1)", "UnpackQ true 24 r (r+1)"),
    ("key entry over-read", r"rax + 160 + 128", r"rax + 160 + 160",
     "direct 0 288", "direct 0 320"),
)


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError(f"expected one mutation site for {old!r}")
    return source.replace(old, new)


def assemble(work, source):
    obj = work / "stage.o"
    subprocess.run(["cc", "-x", "assembler", "-c", "-o", obj, "-"],
                   input=".intel_syntax noprefix\n" + source, text=True, check=True)
    raw = work / "stage.bin"
    subprocess.run(["objcopy", "-O", "binary", "-j", ".text", obj, raw], check=True)
    return raw.read_bytes()


def run(elf, audit, work):
    pc, size = symbol_extent(elf, SYMBOL)
    original = symbol_bytes(elf, pc, size)
    source = SOURCE.read_text()
    symbols = json.loads((audit / "manifest.json").read_text())["symbols"]
    retained, = (audit / item["path"] for item in symbols if item["name"] == SYMBOL)
    if original != retained.read_bytes() or original != assemble(work, source):
        raise ValueError("expected the certified linked stage_round.S symbol")
    for name in ("arithmetic", "curve25519", "machine", "crate"):
        (work / name).symlink_to(audit / name)
    dest = work / "StageRound"
    dest.mkdir()
    shutil.copyfile(audit / "StageRound/Audit.v", dest / "Audit.v")
    shutil.copyfile(HERE / "coq/Counterexample.v", dest / "Counterexample.v")
    listing = (audit / "StageRound/Program.v").read_text()
    for i, (label, old, new, old_op, new_op) in enumerate(MUTANTS):
        damaged = assemble(work, replace_once(source, old, new))
        if len(damaged) != size or damaged == original:
            raise ValueError(f"expected a changed, equal-length symbol for {label}")
        binary = work / "mutant.elf"
        shutil.copyfile(elf, binary)
        with binary.open("r+b") as stream:
            offset = executable_offset(stream, pc, size)
            stream.seek(offset)
            stream.write(damaged)
        raw = dest / "MutantBytes.v"
        write_symbol_bytes(raw, symbol_bytes(binary, pc, size))
        with raw.open("a") as stream:
            stream.write(f"Definition mutation := {i}%nat.\n")
        (dest / "Program.v").write_text(replace_once(listing, old_op, new_op))
        for name in ("Program", "Audit", "MutantBytes", "Counterexample"):
            subprocess.run(["coqc", *component_flags("stage_round"), f"StageRound/{name}.v"],
                           cwd=work, check=True)
        print(f"Coq proved the {label} mutation violates the public contract", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="stage-round-mutations-") as tmp:
        run(args.elf.resolve(), args.audit.resolve(), Path(tmp))
