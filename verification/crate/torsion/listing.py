"""Lift the linked ZIP-215 entry and its local subroutines."""
from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from mask_listing import linked_program

SYMBOL = "ed25519_simd_check_8_torsion_ifma"


def program(binary, dest):
    return linked_program(binary, [(SYMBOL, "code")], dest)[0][2]
