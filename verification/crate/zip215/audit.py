"""Check the ZIP-215 callers and their cryptographic callees in one linked ELF."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from elf import symbol_bytes, symbol_extent
from evidence import sha256, write_evidence
from proof_build import COMPONENTS, MASK_PROJECTS, check_object, compile_libraries, component_flags, write_symbol_bytes

DEPENDENCIES = {
    "radix16": ("Radix16", "Scalar"),
    "full_ladder": ("FullLadder", "StageRound", "LadderStep", "Double4", "CachedAdd"),
    "decompress_r": ("Decode", "Pow2"),
    "dalek_recompress": ("Dalek", "SmallOrder"),
    "torsion": ("Torsion",),
}
ENTRIES = {"Candidate": "candidate", "Scatter": "scatter", "Decoded": "decoded",
           "Push": "push", "CheckR": "check_r", "Flush": "flush"}
FLAGS = component_flags("zip215") + [arg for namespaces in DEPENDENCIES.values()
    for ns in namespaces for arg in ("-Q", ns, "Ed25519Simd." + ns)]


def inputs(elf, dest):
    symbols = []
    modules = []
    for label, suffix in ENTRIES.items():
        name = "ed25519_simd_zip215_" + suffix
        address, size = symbol_extent(elf, name)
        raw = symbol_bytes(elf, address, size)
        module = label + "Bytes"
        path = dest / (module + ".v")
        write_symbol_bytes(path, raw)
        with path.open("a") as f:
            f.write(f"Definition address : Z := {address}.\n")
        symbols.append((name, address, raw))
        modules.append(module)
    return symbols, modules


def replay(elf, work, dependencies, recompress_dependencies=None):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work, projects=MASK_PROJECTS)
    dest = work / "Zip215"
    dest.mkdir()
    symbols, modules = inputs(elf, dest)
    dep_symbols = {}
    digest = sha256(elf)
    components = {ns: component for component, ns in COMPONENTS.items()}
    for name, namespaces in DEPENDENCIES.items():
        parent = recompress_dependencies if name == "dalek_recompress" and recompress_dependencies else dependencies
        audit = parent / (name.replace("_", "-") + "-audit")
        if not audit.exists():
            subprocess.run([sys.executable, "-B", str(HERE.parent / name / "audit.py"),
                            str(elf), "--output", str(audit)], check=True)
        manifest = json.loads((audit / "manifest.json").read_text())
        if manifest["elf"]["sha256"] != digest:
            raise ValueError(f"{audit} was built against a different ELF")
        for symbol in manifest["symbols"]:
            entry = symbol["name"]
            pc, size = symbol_extent(elf, entry)
            raw = symbol_bytes(elf, pc, size)
            if (pc != symbol["address"] or raw != (audit / symbol["path"]).read_bytes()):
                raise ValueError(f"callee evidence differs from ELF for {entry}")
            dep_symbols[entry] = (entry, pc, raw)
        for ns in namespaces:
            for source in (audit / ns).glob("*.v"):
                checked_in = HERE.parent / components[ns] / "coq" / source.name
                if sha256(source) != manifest["files"][f"{ns}/{source.name}"]:
                    raise ValueError(f"corrupt callee proof source {source}")
                if checked_in.exists() and source.read_bytes() != checked_in.read_bytes():
                    raise ValueError(f"callee evidence predates the current {checked_in}")
            shutil.copytree(audit / ns, work / ns, ignore=shutil.ignore_patterns("Checked.*"))
    # The decoder audit also records its pow2 target in DecoderBytes.v.
    # Recheck the one Dalek module importing that richer generated module.
    subprocess.run(["coqc", *FLAGS, "Dalek/Object.v"], cwd=work, check=True)
    for module in (*modules, "Staging", "Caller", "Binding", "Equation", "Calls", "Schedule", "Audit", "Object"):
        path = dest / (module + ".v")
        if module not in modules:
            shutil.copyfile(HERE / "coq" / path.name, path)
        subprocess.run(["coqc", *FLAGS, str(path.relative_to(work))], cwd=work, check=True)
    checks = check_object(work, FLAGS, "zip215")
    asm = VERIFY.parent / "src/wide/avx512ifma"
    write_evidence(elf, work, "zip215", checks, symbols + list(dep_symbols.values()),
                   [asm / "zip215.S", asm / "point_encoding.inc"], FLAGS)
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
