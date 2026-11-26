"""Compose the two pre-hash preparation entries and their same-ELF callees."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from crate.post_hash.build import load_callees, symbol_inputs
from evidence import write_evidence
from proof_build import ED25519_FLAGS, check_object, compile_signature_equations, component_flags

ENTRIES = {"Common": "ed25519_simd_prepare_chunk", "Strict": "ed25519_simd_dalek_prepare_chunk"}
DEPENDENCIES = {
    "dalek_post_hash": ("DalekPostHash", "PostHash", "Zip215", "Dalek", "SmallOrder",
                        "Decode", "Pow2", "FullLadder", "StageRound", "LadderStep",
                        "Double4", "CachedAdd", "Radix16", "Scalar"),
    "key_table": ("KeyTable",),
    "signature_scalar": ("SignatureScalar",),
}
FLAGS = component_flags("prepare_chunk") + ED25519_FLAGS + [
    arg for names in DEPENDENCIES.values() for ns in names for arg in ("-Q", ns, "Ed25519Simd." + ns)]
MODULES = ("Caller", "Staging", "Dispatch", "Composition", "Audit", "Object")


def replay(elf, work, dependencies, dalek):
    work.mkdir(parents=True, exist_ok=False)
    compile_signature_equations(work)
    dest = work / "PrepareChunk"
    dest.mkdir()
    symbols, inputs = symbol_inputs(elf, dest, ENTRIES)
    callees = load_callees(elf, work, dependencies, DEPENDENCIES, {"dalek_post_hash": dalek})
    # The full paired-decoder certificate adds pow_pc to DecoderBytes.
    subprocess.run(["coqc", *FLAGS, "KeyTable/Object.v"], cwd=work, check=True)
    for name in (*inputs, *MODULES):
        if name in MODULES:
            shutil.copyfile(HERE / "coq" / (name + ".v"), dest / (name + ".v"))
        subprocess.run(["coqc", *FLAGS, f"PrepareChunk/{name}.v"], cwd=work, check=True)
    checks = check_object(work, FLAGS, "prepare_chunk")
    asm = VERIFY.parent / "src/wide/avx512ifma"
    write_evidence(elf, work, "prepare_chunk", checks, symbols + callees,
                   [asm / "prepare_chunk.S", asm / "prepare.rs"], FLAGS)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--dependencies", type=Path)
    parser.add_argument("--dalek-dependencies", type=Path)
    args = parser.parse_args()
    work = args.output.resolve()
    deps = (args.dependencies or work.with_name(work.name + "-dependencies")).resolve()
    replay(args.elf.resolve(), work, deps, (args.dalek_dependencies or deps).resolve())
