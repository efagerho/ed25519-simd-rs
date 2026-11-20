"""Kernel-check the scalar certificate against independently supplied bytes."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[1]))
from proof_build import certify_modules

PROOF_MODULES = (
    "ScalarSpec", "ScalarMath", "Symbolic", "Product", "Unpack", "Reduction", "Montgomery",
    "Borrow", "Finish", "Calculate", "ScalarABI", "Lane", "Control", "Routing",
    "ScalarMemory", "FrameProof", "ScalarBytes", "Logical", "Audit", "EntryTests",
)


def certify(raw, work):
    sources = [HERE / "coq" / (module + ".v")
               for module in PROOF_MODULES]
    return certify_modules(raw, work, sources, HERE / "coq/Object.v")
