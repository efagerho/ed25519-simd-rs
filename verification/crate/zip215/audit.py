"""Check the ZIP-215 callers and their cryptographic callees in one linked ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from evidence import write_evidence
from crate.post_hash.build import SHARED_FLAGS, compile_shared, load_callees, symbol_inputs
from proof_build import MASK_PROJECTS, check_object, compile_libraries, component_flags

DEPENDENCIES = {
    "radix16": ("Radix16", "Scalar"),
    "full_ladder": ("FullLadder", "StageRound", "LadderStep", "Double4", "CachedAdd"),
    "decompress_r": ("Decode", "Pow2"),
    "dalek_recompress": ("Dalek", "SmallOrder"),
    "torsion": ("Torsion",),
}
ENTRIES = {"Candidate": "candidate", "Scatter": "scatter", "Decoded": "decoded",
           "Push": "push", "CheckR": "check_r", "Flush": "flush"}
FLAGS = component_flags("zip215") + SHARED_FLAGS + [arg for namespaces in DEPENDENCIES.values()
    for ns in namespaces for arg in ("-Q", ns, "Ed25519Simd." + ns)]


def inputs(elf, dest):
    return symbol_inputs(elf, dest, {k: "ed25519_simd_zip215_" + v for k, v in ENTRIES.items()})


def replay(elf, work, dependencies, recompress_dependencies=None):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work, projects=MASK_PROJECTS)
    dest = work / "Zip215"
    dest.mkdir()
    symbols, modules = inputs(elf, dest)
    overrides = {"dalek_recompress": recompress_dependencies} if recompress_dependencies else {}
    callees = load_callees(elf, work, dependencies, DEPENDENCIES, overrides)
    compile_shared(work, FLAGS)
    for module in (*modules, "Caller", "ScatterTrace", "ScatterMutation", "Binding", "Equation", "Calls", "Schedule", "Audit", "Object"):
        path = dest / (module + ".v")
        if module not in modules:
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *FLAGS, str(path.relative_to(work))], cwd=work, check=True)
    checks = check_object(work, FLAGS, "zip215")
    asm = VERIFY.parent / "src/wide/avx512ifma"
    write_evidence(elf, work, "zip215", checks, symbols + callees,
                   [asm / "zip215.S", asm / "post_hash.inc", asm / "point_encoding.inc"], FLAGS)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--dependencies", type=Path, help="directory of audits from the same ELF")
    parser.add_argument("--recompress-dependencies", type=Path, help="separate Dalek callee audit directory")
    args = parser.parse_args()
    work = args.output.resolve()
    replay(args.elf.resolve(), work, (args.dependencies or work.parent / (work.name + "-dependencies")).resolve(),
           args.recompress_dependencies)
