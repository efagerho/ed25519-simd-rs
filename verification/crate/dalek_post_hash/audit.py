"""Check strict post-hash verification and its callees in one linked ELF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from crate.post_hash.build import SHARED_FLAGS, compile_shared, load_callees, symbol_inputs
from evidence import write_evidence
from proof_build import ED25519_FLAGS, check_object, compile_signature_equations, component_flags

DEPENDENCIES = {
    "radix16": ("Radix16", "Scalar"),
    "full_ladder": ("FullLadder", "StageRound", "LadderStep", "Double4", "CachedAdd"),
    "decompress_r": ("Decode", "Pow2"),
    "dalek_recompress": ("Dalek", "SmallOrder"),
}
ENTRIES = {key: "ed25519_simd_dalek_" + suffix for key, suffix in
           (("Candidate", "candidate"), ("Push", "push"), ("Flush", "flush"),
            ("Decoded", "decoded"), ("Filter", "filter_keys"))}
ENTRIES["Scatter"] = "ed25519_simd_zip215_scatter"
FLAGS = component_flags("dalek_post_hash") + ED25519_FLAGS + SHARED_FLAGS + ["-Q", "Zip215", "Ed25519Simd.Zip215"] + [
    arg for names in DEPENDENCIES.values() for ns in names for arg in ("-Q", ns, "Ed25519Simd." + ns)]


def replay(elf, work, dependencies, overrides):
    work.mkdir(parents=True, exist_ok=False)
    compile_signature_equations(work)
    dest = work / "DalekPostHash"
    dest.mkdir()
    symbols, modules = symbol_inputs(elf, dest, ENTRIES)
    callees = load_callees(elf, work, dependencies, DEPENDENCIES, overrides)
    compile_shared(work, FLAGS)
    (work / "Zip215").mkdir()
    for ns, names, sources in (("Zip215", ["Caller", "ScatterTrace", "Schedule"], HERE.parent / "zip215/coq"),
                               ("DalekPostHash", [*modules, "Caller", "Binding", "Screen", "Keys",
                                "Decoded", "Queue", "Audit", "Object"], HERE / "coq")):
        for name in names:
            path = Path(ns) / (name + ".v")
            if name not in modules:
                shutil.copyfile(sources / path.name, work / path)
            subprocess.run(["coqc", *FLAGS, str(path)], cwd=work, check=True)
    checks = check_object(work, FLAGS, "dalek_post_hash")
    asm = VERIFY.parent / "src/wide/avx512ifma"
    write_evidence(elf, work, "dalek_post_hash", checks, symbols + callees,
                   [asm / n for n in ("dalek.S", "post_hash.inc", "point_encoding.inc")], FLAGS)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--dependencies", type=Path)
    parser.add_argument("--recompress-dependencies", type=Path)
    args = parser.parse_args()
    work = args.output.resolve()
    overrides = {"dalek_recompress": args.recompress_dependencies.resolve()} if args.recompress_dependencies else {}
    replay(args.elf.resolve(), work, (args.dependencies or work.with_name(work.name + "-dependencies")).resolve(), overrides)
