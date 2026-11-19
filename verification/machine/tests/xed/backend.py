"""Ask Intel XED for decoded operand information, including read/write actions."""
import json
from pathlib import Path
import subprocess

from case_data import GPRS, OPS


def expected(instruction, length):
    op, dst, *src = instruction
    operands = [{"action": "RW" if op.startswith("vpmadd52") else "W", "reg": f"ZMM{dst}"}]
    if OPS[op][1].endswith("bd"):
        if op.endswith("_mem"):
            operands.append({"action": "R", "reg": f"ZMM{src[0]}"})
        base, disp = src[-2:]
        operands.append({"action": "R", "base": GPRS[base].upper(), "index": "INVALID",
                         "disp": disp, "size": 64, "address_width": 64})
    else:
        for kind, value in zip(OPS[op][1][1:], src):
            operand = {"reg": f"ZMM{value}"} if kind == "r" else {"imm": value}
            operands.append({"action": "R", **operand})
    return {"op": (op[:-4] if op.endswith("_mem") else op).upper(), "length": length, "width": 512, "mask": 0,
            "zeroing": 0, "broadcast": 0, "evex_b": 0, "encoding": 2,
            "segment_override": 0, "operands": operands}


def decode(kit, work, encodings):
    kit = Path(kit)
    driver = work / "xed-decode"
    subprocess.run(["cc", "-O2", "-I", kit / "include", Path(__file__).with_name("decode.c"),
                    kit / "lib/libxed.a", "-o", driver], check=True)
    data = "\n".join(b.hex() for b in encodings) + "\n"
    rows = subprocess.check_output([driver], input=data, text=True).splitlines()
    if len(rows) != len(encodings):
        raise ValueError("incomplete Intel XED output")
    return list(map(json.loads, rows))
