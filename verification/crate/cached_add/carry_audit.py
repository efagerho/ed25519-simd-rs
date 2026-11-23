"""Check the deferred-carry blocks in a linked double4/cached-add candidate."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from certificate import CARRY_MODULES, HERE
from listing import SOURCES, SYMBOL, generate
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence
from mask_listing import instructions
from proof_build import compile_libraries, component_flags, write_symbol_bytes

DOUBLE = "ed25519_simd_double4_ifma"
FLAGS = component_flags("cached_add")


def locate(rows, predicate):
    matches = [pc for pc, (_, op, args) in rows.items() if predicate(op, args)]
    if len(matches) != 1:
        raise ValueError(f"expected one instruction site, found {len(matches)}")
    return matches[0]


def pair_start(rows, reg):
    # The comparison follows the five RHS loads. Coq checks the opcode,
    # register, tag, jump displacement and both complete vector sequences.
    cmp_pc = locate(rows, lambda op, args: op == "cmp" and args.startswith(reg + ","))
    pcs = sorted(rows)
    index = pcs.index(cmp_pc)
    if index < 5:
        raise ValueError("missing pair prologue")
    return pcs[index - 5]


def inspect(elf, dest):
    bodies, symbols = [], []
    for symbol, module in ((DOUBLE, "CandidateDouble"), (SYMBOL, "CandidateAdd")):
        base, size = symbol_extent(elf, symbol)
        raw = symbol_bytes(elf, base, size)
        symbols.append((symbol, base, raw))
        write_symbol_bytes(dest / (module + ".v"), raw)
        bodies.append((base, instructions(elf, symbol)))
    (double_base, double), (add_base, add) = bodies
    ab = locate(add, lambda op, args: op == "vmovdqu64" and args == "zmm0,ZMMWORD PTR [rdi]")
    cd = locate(add, lambda op, args: (op, args) == ("dec", "ecx"))
    call = locate(add, lambda op, args: op == "call" and int(args.split()[0], 16) == cd)
    jump = locate(add, lambda op, args: op == "jmp")
    raw_c = int(add[jump][2].split()[0], 16)
    offsets = [pair_start(double, "ecx") - double_base]
    offsets.extend(pc - add_base for pc in (pair_start(add, "edx"), ab, call, cd, raw_c))
    for base, rows in bodies:
        for address in ("[rdi]", "[rdi+0x140]"):
            args = f"ZMMWORD PTR {address},zmm0"
            offsets.append(locate(rows, lambda op, operands: (op, operands) == ("vmovdqu64", args)) - base)
    if min(offsets) < 0:
        raise ValueError("instruction site precedes symbol")
    (dest / "CandidateSites.v").write_text(
        "From Ed25519Simd.CachedAdd Require Import CarryImage.\n"
        "Definition sites := Sites " + " ".join(f"{n}%nat" for n in offsets) + ".\n")
    return symbols


def replay(elf, work):
    compile_libraries(work)
    dest = work / "CachedAdd"
    dest.mkdir()
    generate(dest)  # The reference listing supplies vector programs, checked against candidate bytes.
    symbols = inspect(elf, dest)
    for name in (*CARRY_MODULES, "CarryObject"):
        shutil.copyfile(HERE / "coq" / (name + ".v"), dest / (name + ".v"))
    for name in ("Program", *CARRY_MODULES, "CandidateDouble", "CandidateAdd", "CandidateSites", "CarryObject"):
        subprocess.run(["coqc", *FLAGS, f"CachedAdd/{name}.v"], cwd=work, check=True)
    (dest / "CarryChecked.v").write_text(
        "From Ed25519Simd.CachedAdd Require CarryImage CarryObject CandidateDouble CandidateAdd CandidateSites.\n"
        "Definition checked : CarryImage.carry_block_contract CandidateDouble.symbol_bytes "
        "CandidateAdd.symbol_bytes CandidateSites.sites := CarryObject.linked_deferred_carry_correct.\n"
        "Print Assumptions checked.\n")
    output = subprocess.check_output(["coqc", *FLAGS, "CachedAdd/CarryChecked.v"], cwd=work, text=True)
    if output.strip() != "Closed under the global context":
        raise ValueError(f"unexpected proof assumptions: {output}")
    (work / "assumptions.txt").write_text(output)
    command = ["coqchk", *FLAGS, "-silent", "Ed25519Simd.CachedAdd.CarryChecked"]
    with (work / "coqchk.log").open("w") as log:
        subprocess.run(command, cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    checks = {"theorem": "Ed25519Simd.CachedAdd.CarryObject.linked_deferred_carry_correct",
              "assumptions": output.strip(), "coqchk": {"command": command, "exit_code": 0}}
    write_evidence(elf, work, "cached_add", checks, symbols,
                   (*SOURCES, HERE.parents[1] / "mask_listing.py"), FLAGS)
    print(f"Checked linked_deferred_carry_correct against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, help="retain the proof in a fresh directory")
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
        replay(args.elf.resolve(), args.output.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="carry-blocks-") as directory:
            replay(args.elf.resolve(), Path(directory))
