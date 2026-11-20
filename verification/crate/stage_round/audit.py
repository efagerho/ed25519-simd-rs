"""Check the table-selection and staging theorem against the linked release symbol."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence
from proof_build import check_object, compile_libraries, component_flags, write_symbol_bytes

SYMBOL = "ed25519_simd_stage_round"
SOURCE = VERIFY.parent / "src/wide/avx512ifma/stage_round.S"


def audit(elf, work):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work)
    dest = work / "StageRound"
    dest.mkdir()
    pc, size = symbol_extent(elf, SYMBOL)
    raw = symbol_bytes(elf, pc, size)
    flags = component_flags("stage_round")
    write_symbol_bytes(dest / "ObjectBytes.v", raw)
    for name in ("ObjectBytes", "Program", "Audit", "Routing", "Selection", "Execution", "Object"):
        path = dest / (name + ".v")
        if name != "ObjectBytes":
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *flags, str(path.relative_to(work))], cwd=work, check=True)
    checks = check_object(work, flags, "stage_round")
    write_evidence(elf, work, "stage_round", checks, [(SYMBOL, pc, raw)], [SOURCE, HERE / "coq/Counterexample.v"], flags)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    audit(args.elf.resolve(), args.output.resolve())
