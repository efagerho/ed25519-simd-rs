"""Decode every byte of the linked pow2 symbol using GNU binutils."""
import re
import sys
from pathlib import Path
import subprocess

sys.path.append(str(Path(__file__).resolve().parents[2]))
from elf import require, symbol_extent

SYMBOL = "ed25519_simd_pow2_ifma"


def disassemble(binary, symbol=SYMBOL):
    start, size = symbol_extent(binary, symbol)
    dump = subprocess.check_output(["objdump", "-dz", "-M", "intel", "--insn-width=16",
                                    "--disassemble=" + symbol, binary], text=True)
    code = {}
    expected = start
    for line in dump.splitlines():
        m = re.fullmatch(r"\s*([0-9a-f]+):\s*((?:[0-9a-f]{2} )+)\s*(\S+)(?:\s+(.*?))?\s*", line)
        if not m:
            continue
        pc = int(m[1], 16)
        require(pc == expected, "gap in decoded instructions")
        expected += len(bytes.fromhex(m[2]))
        operands = (m[4] or "").split(" <")[0].replace("ZMMWORD PTR ", "")
        code[pc] = (expected, m[3], operands.split(",") if operands else [])
    require(expected == start + size, "incomplete disassembly")
    return start, code


def address(operand):
    m = re.fullmatch(r"\[(rsp|rdi|rsi|rdx|r8)(?:\+(0x[0-9a-f]+))?\]", operand)
    require(m, "unexpected address " + operand)
    return m[1], int(m[2] or "0", 0)
