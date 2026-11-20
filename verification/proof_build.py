"""Compile shared Coq libraries and kernel-check a concrete object certificate."""
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LIBRARIES = (("arithmetic", "ProofArithmetic"), ("machine", "Machine"),
             ("curve25519", "Curve25519"), ("crate", "Ed25519Simd"))
COMPONENTS = {"pow2": "Pow2", "double4": "Double4", "cached_add": "CachedAdd",
              "scalar": "Scalar", "ladder_step": "LadderStep"}


def library_flags(prefix=Path(".")):
    return [arg for directory, namespace in LIBRARIES
            for arg in ("-Q", str(prefix / directory), namespace)]


def component_flags(name, directory=None, prefix=Path(".")):
    namespace = COMPONENTS[name]
    return ["-Q", str(directory or namespace), "Ed25519Simd." + namespace, *library_flags(prefix)]


def compile_library(source, dest):
    dest.mkdir(parents=True, exist_ok=True)
    project = source / "_CoqProject"
    shutil.copyfile(project, dest / project.name)
    flags = []
    for line in project.read_text().splitlines():
        if line.startswith("-Q "):
            flags.extend(line.split())
        elif line.endswith(".v"):
            target = dest / line
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / line, target)
    ordered = subprocess.check_output(["coqdep", "-sort", "-f", "_CoqProject"], cwd=dest, text=True)
    for path in ordered.split():
        subprocess.run(["coqc", *flags, path], cwd=dest, check=True)


def compile_libraries(work):
    for directory in ("arithmetic", "curve25519", "machine", "machine/symbolic", "crate"):
        compile_library(HERE / directory, work / directory)


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
    return subprocess.check_output(["coqc", *flags, object_source.name], cwd=work, text=True)


def certify_modules(raw, work, modules, object_source):
    component = object_source.parent.parent.name
    compile_libraries(work)
    dest = work / COMPONENTS[component]
    dest.mkdir()
    (work / "Program.v").rename(dest / "Program.v")
    assumptions = compile_object(raw, dest, modules, object_source,
                                 component_flags(component, ".", Path("..")))
    return check_object(work, component_flags(component), assumptions, component)


def check_object(work, flags, assumptions, component):
    (work / "assumptions.txt").write_text(assumptions)
    if assumptions.strip() != "Closed under the global context":
        raise ValueError(f"unexpected proof assumptions: {assumptions}")
    command = ["coqchk", *flags, "-silent", f"Ed25519Simd.{COMPONENTS[component]}.Object"]
    with (work / "coqchk.log").open("w") as log:
        result = subprocess.run(command, cwd=work, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        sys.stderr.write((work / "coqchk.log").read_text())
        result.check_returncode()
    return {"assumptions": assumptions.strip(), "coqchk": {"command": command, "exit_code": 0}}
