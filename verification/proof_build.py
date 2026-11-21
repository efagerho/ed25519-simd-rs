"""Compile shared Coq libraries and kernel-check a concrete object certificate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
LIBRARIES = (("arithmetic", "ProofArithmetic"), ("machine", "Machine"),
             ("curve25519", "Curve25519"), ("crate", "Ed25519Simd"))
SHARED_PROJECTS = ("arithmetic", "curve25519", "machine", "machine/symbolic", "crate")
GROUP_PROJECTS = (*SHARED_PROJECTS, "curve25519/group")
MASK_PROJECTS = (*GROUP_PROJECTS, "crate/field51")
SHARED_ENV = "ED25519_SIMD_COQ_LIBRARIES"
COMPONENTS = {"pow2": "Pow2", "double4": "Double4", "cached_add": "CachedAdd",
              "scalar": "Scalar", "ladder_step": "LadderStep", "torsion": "Torsion",
              "small_order": "SmallOrder", "radix16": "Radix16", "stage_round": "StageRound",
              "full_ladder": "FullLadder", "decompress_r": "Decode", "dalek_recompress": "Dalek"}


# The release statement is independent of the theorem implementation in Object.v.
PUBLIC_THEOREMS = {
    "pow2": ("assembled_symbol_correct", "pow2_contract"),
    "double4": ("assembled_double4_correct", "double4_contract"),
    "cached_add": ("assembled_cached_add_correct", "cached_add_contract"),
    "scalar": ("assembled_scalar_correct", "scalar_contract"),
    "stage_round": ("assembled_stage_round_correct", "stage_contract"),
    "radix16": ("assembled_digest_to_radix16_correct", "digest_contract"),
    "ladder_step": ("assembled_ladder_step_correct", "ladder_contract"),
    "full_ladder": ("assembled_full_ladder_correct", "full_ladder_contract"),
    "small_order": ("assembled_small_order_correct", "small_order_contract"),
    "dalek_recompress": ("assembled_dalek_recompress_correct", "recompress_contract"),
    "decompress_r": ("assembled_decode_correct", "decode_contract"),
    "torsion": ("assembled_torsion_correct", "torsion_contract"),
}


def public_statement(component):
    namespace = "Ed25519Simd." + COMPONENTS[component]
    theorem, contract = PUBLIC_THEOREMS[component]
    expected = f"{namespace}.Audit.{contract}"
    if component == "dalek_recompress":
        for module in ("Dalek.ObjectBytes", "Decode.DecoderBytes", "Decode.HelperBytes", "SmallOrder.EntryBytes"):
            expected += f" Ed25519Simd.{module}.address Ed25519Simd.{module}.symbol_bytes"
    elif component == "decompress_r":
        for module in ("DecoderBytes", "HelperBytes"):
            expected += f" {namespace}.{module}.address {namespace}.{module}.symbol_bytes"
        expected += f" {namespace}.DecoderBytes.pow_pc Ed25519Simd.Pow2.ObjectBytes.symbol_bytes"
    elif component == "small_order":
        for module in ("EntryBytes", "HelperBytes"):
            expected += f" {namespace}.{module}.address {namespace}.{module}.symbol_bytes"
    elif component == "radix16":
        expected += (f" {namespace}.LinkedBytes.wrapper_pc {namespace}.LinkedBytes.symbol_bytes"
                     f" {namespace}.LinkedBytes.reducer_pc Ed25519Simd.Scalar.ObjectBytes.symbol_bytes")
    elif component not in ("ladder_step", "full_ladder"):
        expected += f" {namespace}.ObjectBytes.symbol_bytes"
    return f"{namespace}.Object.{theorem}", expected


def library_flags(prefix=Path(".")):
    return [arg for directory, namespace in LIBRARIES
            for arg in ("-Q", str(prefix / directory), namespace)]


def component_flags(name, directory=None, prefix=Path(".")):
    namespace = COMPONENTS[name]
    return ["-Q", str(directory or namespace), "Ed25519Simd." + namespace, *library_flags(prefix)]


def stage_sources(source, work, projects):
    files = []
    for directory in projects:
        project = Path(directory) / "_CoqProject"
        files.append(project)
        files.extend(project.parent / line for line in (source / project).read_text().splitlines()
                     if line.endswith(".v"))
    for path in files:
        dest = work / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / path, dest)
    return files


def compile_project(dest):
    flags = [arg for line in (dest / "_CoqProject").read_text().splitlines()
             if line.startswith("-Q ") for arg in line.split()]
    ordered = subprocess.check_output(["coqdep", "-sort", "-f", "_CoqProject"], cwd=dest, text=True)
    for path in ordered.split():
        subprocess.run(["coqc", *flags, path], cwd=dest, check=True)


def compiler_version():
    return subprocess.check_output(["coqc", "--version"], text=True).strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare_shared_libraries(destination, jobs):
    """Publish a fresh job-local build only after every shared .vo is complete."""
    if destination.exists():
        raise FileExistsError(f"choose a new directory for shared libraries: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as tmp:
        work = Path(tmp) / "build"
        inputs = stage_sources(HERE, work, MASK_PROJECTS)
        sources = [p for p in inputs if p.suffix == ".v"]
        write_project(work, library_flags(), [work / p for p in sources])
        subprocess.run(["coq_makefile", "-f", "_CoqProject", "-o", "Makefile"], cwd=work, check=True)
        objects = [p.with_suffix(".vo") for p in sources]
        subprocess.run(["make", "-j", str(jobs), *map(str, objects)], cwd=work, check=True)
        manifest = {"coqc": compiler_version(),
                    "files": {str(p): digest(work / p) for p in inputs + objects}}
        (work / "shared.json").write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
        work.rename(destination)


def compile_libraries(work, projects=SHARED_PROJECTS, source=HERE):
    inputs = stage_sources(source, work, projects)
    shared = os.environ.get(SHARED_ENV)
    if not shared:
        for directory in projects:
            compile_project(work / directory)
        return

    prepared = Path(shared)
    manifest = json.loads((prepared / "shared.json").read_text())
    if compiler_version() != manifest["coqc"]:
        raise ValueError("shared libraries were built with a different coqc")
    # Keep the checkout's sources in each audit. Copy only their compiled objects,
    # including when the caller is a mutation test with its own source tree.
    for path in inputs:
        if digest(work / path) != manifest["files"].get(str(path)):
            raise ValueError(f"shared Coq build does not match source {path}")
        if path.suffix == ".v":
            obj = path.with_suffix(".vo")
            data = (prepared / obj).read_bytes()
            if hashlib.sha256(data).hexdigest() != manifest["files"].get(str(obj)):
                raise ValueError(f"shared Coq object failed its digest check: {obj}")
            (work / obj).write_bytes(data)


def write_project(work, flags, sources):
    lines = [" ".join(flags[i:i+3]) for i in range(0, len(flags), 3)]
    lines.extend(str(path.relative_to(work)) for path in sources)
    (work / "_CoqProject").write_text("\n".join(lines) + "\n")


def write_symbol_bytes(path, raw):
    chunks = []
    for i in range(0, len(raw), 32):
        chunks.append("[" + ";".join(f"0x{x:02x}" for x in raw[i:i+32]) + "]")
    source = """From Coq Require Import List ZArith.
Import ListNotations. Open Scope Z_scope.
Definition symbol_bytes : list Z := concat [\n""" + ";\n".join(chunks) + "].\n"
    path.write_text(source)


def compile_object(raw, work, modules, object_source, flags):
    subprocess.run(["coqc", *flags, "Program.v"], cwd=work, check=True)
    for source in modules:
        shutil.copyfile(source, work / source.name)
        subprocess.run(["coqc", *flags, source.name], cwd=work, check=True)
    write_symbol_bytes(work / "ObjectBytes.v", raw)
    subprocess.run(["coqc", *flags, "ObjectBytes.v"], cwd=work, check=True)
    shutil.copyfile(object_source, work / object_source.name)
    subprocess.run(["coqc", *flags, object_source.name], cwd=work, check=True, stdout=subprocess.DEVNULL)


def certify_modules(raw, work, modules, object_source, projects=SHARED_PROJECTS):
    component = object_source.parent.parent.name
    compile_libraries(work, projects=projects)
    dest = work / COMPONENTS[component]
    dest.mkdir()
    (work / "Program.v").rename(dest / "Program.v")
    compile_object(raw, dest, modules, object_source, component_flags(component, ".", Path("..")))
    return check_object(work, component_flags(component), component)


def check_object(work, flags, component):
    namespace = "Ed25519Simd." + COMPONENTS[component]
    theorem, expected = public_statement(component)
    checked = Path(COMPONENTS[component]) / "Checked.v"
    (work / checked).write_text(f"Require {namespace}.Object.\n"
                                f"Definition checked : {expected} := {theorem}.\n"
                                "Print Assumptions checked.\n")
    assumptions = subprocess.check_output(["coqc", *flags, str(checked)], cwd=work, text=True)
    (work / "assumptions.txt").write_text(assumptions)
    if assumptions.strip() != "Closed under the global context":
        raise ValueError(f"unexpected proof assumptions: {assumptions}")
    command = ["coqchk", *flags, "-silent", f"{namespace}.Checked"]
    with (work / "coqchk.log").open("w") as log:
        result = subprocess.run(command, cwd=work, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        sys.stderr.write((work / "coqchk.log").read_text())
        result.check_returncode()
    return {"theorem": f"{theorem} : {expected}", "assumptions": assumptions.strip(), "coqchk": {"command": command, "exit_code": 0}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Build shared Coq libraries for one CI job.")
    parser.add_argument("destination", type=Path, help="new directory for the compiled libraries")
    parser.add_argument("--jobs", type=int, default=4, help="maximum parallel coqc processes")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    prepare_shared_libraries(args.destination.resolve(), args.jobs)
