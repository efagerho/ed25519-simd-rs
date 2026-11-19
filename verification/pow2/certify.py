"""Replay the Coq proof with an equality against independently supplied bytes."""
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
PROOF_MODULES = ("FieldSpec", "Polynomial", "Pow2Caller", "Lane", "Chain", "Buffers",
                 "Pow2ABI", "Pow2Memory", "Pow2Bytes", "ByteEntryTests", "Audit",
                 "FrameProof", "Linked", "Execution")
LOAD_PATH = ("-Q", "machine", "Machine")


def compile_machine(dest):
    source = HERE.parent / "machine"
    dest.mkdir()
    shutil.copyfile(source / "_CoqProject", dest / "_CoqProject")
    for path in source.rglob("*.v"):
        target = dest / path.relative_to(source)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    ordered = subprocess.check_output(["coqdep", "-sort", "-f", "_CoqProject"], cwd=dest, text=True)
    for path in ordered.split():
        subprocess.run(["coqc", "-Q", ".", "Machine", path], cwd=dest, check=True)


def certify(raw, work):
    compile_machine(work / "machine")
    subprocess.run(["coqc", *LOAD_PATH, "Program.v"], cwd=work, check=True)
    for module in PROOF_MODULES:
        name = module + ".v"
        shutil.copyfile(HERE / "coq" / name, work / name)
        subprocess.run(["coqc", *LOAD_PATH, name], cwd=work, check=True)
    chunks = []
    for i in range(0, len(raw), 32):
        chunks.append("[" + ";".join(f"0x{x:02x}" for x in raw[i:i+32]) + "]")
    source = """From Coq Require Import List ZArith.
Import ListNotations. Open Scope Z_scope.
Definition symbol_bytes : list Z := concat [\n""" + ";\n".join(chunks) + "].\n"
    (work / "ObjectBytes.v").write_text(source)
    subprocess.run(["coqc", *LOAD_PATH, "ObjectBytes.v"], cwd=work, check=True)
    shutil.copyfile(HERE / "coq/Object.v", work / "Object.v")
    assumptions = subprocess.check_output(["coqc", *LOAD_PATH, "Object.v"], cwd=work, text=True)
    if assumptions.strip() != "Closed under the global context":
        raise ValueError(f"unexpected proof assumptions: {assumptions}")
    subprocess.run(["coqchk", *LOAD_PATH, "-silent", "Object"], cwd=work, check=True)
