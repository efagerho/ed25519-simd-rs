"""Kernel-check the cached_add certificate against independently supplied bytes."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[1]))
from proof_build import certify_modules

PROOF_MODULES = (
    "CachedAddABI", "CachedAddMemory", "Lane",
    "Control", "Kernels", "KernelInterface", "Bounds", "KernelCalls", "Calls", "Routing",
    "CachedAddSpec", "Arithmetic", "Logical", "FrameProof", "CachedAddBytes", "ReadFootprint",
    "Audit", "EntryTests",
)


def proof_sources():
    return [HERE / "coq" / (module + ".v") for module in PROOF_MODULES]


def certify(raw, work):
    return certify_modules(raw, work, proof_sources(), HERE / "coq/Object.v")
