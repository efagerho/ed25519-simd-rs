"""Kernel-check the cached_add certificate against independently supplied bytes."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[1]))
from proof_build import certify_modules

CARRY_MODULES = (
    "CachedAddABI", "Lane", "Control", "Kernels", "KernelInterface", "Bounds", "KernelCalls",
    "CarryHandoff", "CarryStores", "CarryImage",
)
PROOF_MODULES = (
    *CARRY_MODULES, "CachedAddMemory", "Calls", "Routing", "CachedAddSpec", "Arithmetic",
    "Logical", "FrameProof", "CachedAddBytes", "ReadFootprint", "Audit", "EntryTests",
)


def proof_sources():
    return [HERE / "coq" / (module + ".v") for module in PROOF_MODULES]


def certify(raw, work):
    return certify_modules(raw, work, proof_sources(), HERE / "coq/Object.v")
