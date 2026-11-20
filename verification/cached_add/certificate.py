"""Kernel-check the cached_add certificate against independently supplied bytes."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parent))
from proof_build import LOAD_PATH, certify_modules

PROOF_MODULES = (
    "FieldSpec", "Polynomial", "Symbolic", "CachedAddABI", "CachedAddMemory", "Lane",
    "Control", "Kernels", "KernelInterface", "Bounds", "KernelCalls", "Calls", "Routing",
    "CachedAddSpec", "Arithmetic", "Logical", "FrameProof", "CachedAddBytes", "ReadFootprint",
    "Audit", "EntryTests",
)


def proof_sources():
    return [(HERE.parent / "pow2/coq" if module in ("FieldSpec", "Polynomial")
                  else HERE.parent / "double4/coq" if module == "Symbolic"
                  else HERE / "coq") / (module + ".v")
               for module in PROOF_MODULES]


def certify(raw, work):
    return certify_modules(raw, work, proof_sources(), HERE / "coq/Object.v")
