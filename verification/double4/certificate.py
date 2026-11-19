"""Kernel-check the complete double4 certificate against independently supplied bytes."""
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parent / "pow2"))
from certify import compile_machine

LOAD_PATH = ("-Q", "machine", "Machine")
PROOF_MODULES = ("Bounds", "Interval", "Symbolic", "Double4ABI", "Double4Memory",
                 "Kernels", "KernelInterface", "Round", "Double4Spec", "RoundArithmetic",
                 "Preparation", "Finish", "Execution", "Logical", "FrameProof",
                 "Double4Bytes", "ReadFootprint", "Audit", "EntryTests")


def certify(raw, work):
    compile_machine(work / "machine")
    for module in ("Program", "FieldSpec", "Polynomial", *PROOF_MODULES):
        if module != "Program":
            source = (HERE.parent / "pow2/coq" if module in ("FieldSpec", "Polynomial")
                      else HERE / "coq") / (module + ".v")
            shutil.copyfile(source, work / source.name)
        subprocess.run(["coqc", *LOAD_PATH, module + ".v"], cwd=work, check=True)
    chunks = ["[" + ";".join(f"0x{x:02x}" for x in raw[i:i+32]) + "]"
              for i in range(0, len(raw), 32)]
    (work / "ObjectBytes.v").write_text(
        "From Coq Require Import List ZArith.\nImport ListNotations. Open Scope Z_scope.\n"
        "Definition symbol_bytes : list Z := concat [\n" + ";\n".join(chunks) + "].\n")
    subprocess.run(["coqc", *LOAD_PATH, "ObjectBytes.v"], cwd=work, check=True)
    shutil.copyfile(HERE / "coq/Object.v", work / "Object.v")
    assumptions = subprocess.check_output(["coqc", *LOAD_PATH, "Object.v"], cwd=work, text=True)
    (work / "assumptions.txt").write_text(assumptions)
    if assumptions.strip() != "Closed under the global context":
        raise ValueError(f"unexpected proof assumptions: {assumptions}")
    command = ["coqchk", *LOAD_PATH, "-silent", "Object"]
    with (work / "coqchk.log").open("w") as log:
        result = subprocess.run(command, cwd=work, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        sys.stderr.write((work / "coqchk.log").read_text())
        result.check_returncode()
    return {"assumptions": assumptions.strip(), "coqchk": {"command": command, "exit_code": 0}}
