"""Kernel-check the pow2 certificate against independently supplied bytes."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[1]))
from proof_build import LOAD_PATH, certify_modules

PROOF_MODULES = (
    "FieldSpec", "Polynomial", "Pow2Caller", "Lane", "Chain", "Buffers", "Pow2ABI",
    "Pow2Memory", "Pow2Bytes", "Audit", "ByteEntryTests", "Linked", "Execution", "FrameProof",
)


def certify(raw, work):
    sources = [HERE / "coq" / (module + ".v")
               for module in PROOF_MODULES]
    return certify_modules(raw, work, sources, HERE / "coq/Object.v")
