"""Replay all five linked symbols and check the full-ladder theorem."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
sys.path.insert(0, str(HERE.parent))
from ladder_step.audit import compile_ladder
from stage_round.audit import compile_stage, SOURCE as STAGE_SOURCE
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence
from proof_build import GROUP_PROJECTS, check_object, compile_libraries, write_symbol_bytes

SYMBOL = "ed25519_simd_mul_s_base_minus_k_public"
SOURCE = VERIFY.parent / "src/wide/avx512ifma/mul_s_base_minus_k_public.S"
MODULES = ("LinkedBytes", "StageEntry", "TopCall", "ScalarAction", "Seed", "SeedPath", "SeedProjection", "NativeSeed", "Program", "Operands", "RoundOperands", "Execution",
           "SeedPoint", "Native", "Composition", "Progress", "Audit", "TopPoint", "TopPair", "FirstStage", "LoopFrame", "LoopSlots", "LoopStageCall", "LoopStage", "Object", "NegativeControls")


def compile_full(elf, work, flags):
    _, stage = compile_stage(elf, work)
    flags.extend(["-Q", "StageRound", "Ed25519Simd.StageRound", "-Q", "FullLadder", "Ed25519Simd.FullLadder"])
    dest = work / "FullLadder"
    dest.mkdir()
    pc, size = symbol_extent(elf, SYMBOL)
    raw = symbol_bytes(elf, pc, size)
    linked = dest / "LinkedBytes.v"
    write_symbol_bytes(linked, raw)
    with linked.open("a") as f:
        f.write(f"Definition entry_pc := {pc}%Z.\nDefinition stage_pc := {stage[1]}%Z.\n")
    for name in MODULES:
        path = dest / (name + ".v")
        if name != "LinkedBytes":
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *flags, str(path.relative_to(work))], cwd=work, check=True)
    return flags, [(SYMBOL, pc, raw), stage]


def audit(elf, work):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work, projects=GROUP_PROJECTS)
    flags, helpers, sources = compile_ladder(elf, work)
    flags, full = compile_full(elf, work, flags)
    checks = check_object(work, flags, "full_ladder")
    write_evidence(elf, work, "full_ladder", checks, [*full, *helpers],
                   [SOURCE, STAGE_SOURCE, *sources], flags)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    audit(args.elf.resolve(), args.output.resolve())
