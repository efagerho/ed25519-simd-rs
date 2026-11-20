"""Compile shared Coq libraries and kernel-check a concrete object certificate."""
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LOAD_PATH = ("-Q", "machine", "Machine", "-Q", "arithmetic", "ProofArithmetic")


def compile_library(source, dest, namespace, dependencies=()):
    dest.mkdir()
    shutil.copyfile(source / "_CoqProject", dest / "_CoqProject")
    for path in source.rglob("*.v"):
        target = dest / path.relative_to(source)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    ordered = subprocess.check_output(["coqdep", "-sort", "-f", "_CoqProject"], cwd=dest, text=True)
    for path in ordered.split():
        subprocess.run(["coqc", "-Q", ".", namespace, *dependencies, path], cwd=dest, check=True)


def compile_machine(dest):
    compile_library(HERE / "machine", dest, "Machine")


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
    compile_machine(work / "machine")
    compile_library(HERE / "arithmetic", work / "arithmetic", "ProofArithmetic",
                    ("-Q", "../machine", "Machine"))
    assumptions = compile_object(raw, work, modules, object_source, LOAD_PATH)
    return check_object(work, LOAD_PATH, assumptions)


def check_object(work, flags, assumptions):
    (work / "assumptions.txt").write_text(assumptions)
    if assumptions.strip() != "Closed under the global context":
        raise ValueError(f"unexpected proof assumptions: {assumptions}")
    command = ["coqchk", *flags, "-silent", "Object"]
    with (work / "coqchk.log").open("w") as log:
        result = subprocess.run(command, cwd=work, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        sys.stderr.write((work / "coqchk.log").read_text())
        result.check_returncode()
    return {"assumptions": assumptions.strip(), "coqchk": {"command": command, "exit_code": 0}}
