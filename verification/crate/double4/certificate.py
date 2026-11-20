"""Kernel-check the double4 certificate against independently supplied bytes."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[1]))
from proof_build import LOAD_PATH, certify_modules

PROOF_MODULES = (
    "FieldSpec", "Polynomial", "Bounds", "Symbolic", "Double4ABI", "Double4Memory", "Kernels",
    "KernelInterface", "Round", "Double4Spec", "RoundArithmetic", "Preparation", "Finish",
    "Execution", "Logical", "FrameProof", "Double4Bytes", "ReadFootprint", "Audit",
    "EntryTests",
)


def proof_sources():
    return [(HERE.parent / "pow2/coq" if module in ("FieldSpec", "Polynomial")
                  else HERE / "coq") / (module + ".v")
               for module in PROOF_MODULES]


def certify(raw, work):
    return certify_modules(raw, work, proof_sources(), HERE / "coq/Object.v")
