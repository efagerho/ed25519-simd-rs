"""Lift reachable instructions. Coq re-encodes them against the complete ELF symbol."""
from pathlib import Path
import re
import subprocess
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from elf import symbol_bytes, symbol_extent

SYMBOL = "ed25519_simd_check_8_torsion_ifma"
VECTOR_OPS = {
    "vmovdqa64": "Copy", "vpaddq": "Add", "vpsubq": "Sub", "vpmullq": "Mul",
    "vpandq": "And", "vpxorq": "Xor", "vpsrlq": "Shr",
    "vpmadd52luq": "Madd false", "vpmadd52huq": "Madd true",
}
FIXED = {
    ("push", "rbp"): "PushBP", ("pop", "rbp"): "PopBP",
    ("mov", "rbp,rsp"): "SetBP", ("mov", "rsp,rbp"): "RestoreSP",
    ("and", "rsp,0xffffffffffffffc0"): "AlignSP", ("vzeroupper", ""): "VZeroUpper",
    ("ret", ""): "Return",
}


def address(operand):
    match = re.fullmatch(r"\[(rdi|rsi|rsp|rip)([+-]0x[0-9a-f]+)?\]", operand)
    if not match:
        raise ValueError(f"unsupported memory operand {operand}")
    return match[1], int(match[2] or "0", 0)


def register(operand):
    match = re.fullmatch(r"(?:k|zmm)([0-9]+)", operand)
    if not match:
        raise ValueError(f"expected a vector or mask register, got {operand}")
    return int(match[1])


def instruction(op, args):
    if (op, args) in FIXED:
        return FIXED[op, args]
    operands = args.replace("ZMMWORD PTR ", "").replace("QWORD PTR ", "").split(",")
    dst, src = operands[:2]
    bases = {"rsp": 4, "rsi": 6, "rdi": 7}
    if op == "vpbroadcastq":
        base, disp = address(src)
        if base != "rip":
            raise ValueError(f"expected an image-relative broadcast, got {src}")
        return f"RipBroadcast {register(dst)} ({disp})"
    if op == "vmovdqu64":
        if dst.startswith("["):
            base, disp = address(dst)
            return f"Store {register(src)} {bases[base]} ({disp})"
        base, disp = address(src)
        return f"Vector ({register(dst)}%nat,Load {bases[base]} ({disp}))"
    if op in ("vpcmpeqq", "korw"):
        coq = "CompareQ" if op == "vpcmpeqq" else "OrMask"
        return coq + " " + " ".join(str(register(v)) for v in operands)
    if op == "kmovw" and dst == "eax":
        return f"KmovEax {register(src)}"
    if op == "cmp" and dst == "eax":
        return f"CmpEax {int(src, 0)}"
    if op == "sub" and dst == "rsp":
        return f"SubSP ({int(src, 0)})"
    if op in ("vpaddq", "vpsubq") and operands[2].startswith("["):
        base, disp = address(operands[2])
        sub = "true" if op == "vpsubq" else "false"
        return f"MemALU {sub} {register(dst)} {register(src)} {bases[base]} ({disp})"
    if op in VECTOR_OPS:
        args = [int(v, 0) if v.startswith("0x") or v.isdigit() else register(v)
                for v in operands[1:]]
        return f"Vector ({register(dst)}%nat,{VECTOR_OPS[op]} {' '.join(map(str, args))})"
    raise ValueError(f"unsupported instruction {op} {args}")


def literal(data):
    return "Literal [" + ";".join(map(str, data)) + "]"


def program(binary, dest):
    start, size = symbol_extent(binary, SYMBOL)
    raw = symbol_bytes(binary, start, size)
    dump = subprocess.check_output(["objdump", "-dz", "-Mintel", "--insn-width=16",
                                    "--disassemble=" + SYMBOL, binary], text=True)
    rows = {}
    for line in dump.splitlines():
        match = re.fullmatch(r"\s*([0-9a-f]+):\s*((?:[0-9a-f]{2} )+)\s*(\S+)(?:\s+(.*))?", line)
        if match:
            pc = int(match[1], 16) - start
            end = pc + len(bytes.fromhex(match[2]))
            rows[pc] = end, match[3], (match[4] or "").partition("#")[0].strip()

    reachable = {}
    todo = [0]
    while todo:
        pc = todo.pop()
        if pc in reachable:
            continue
        if pc not in rows or not 0 <= pc < size:
            raise ValueError(f"no instruction at reachable symbol offset {pc:#x}")
        end, op, args = rows[pc]
        if op in ("je", "call"):
            target = int(args.split()[0], 16) - start
            todo.append(target)
            coq = "Je" if op == "je" else "Call"
            decoded = f"{coq} ({target-end})"
        else:
            decoded = instruction(op, args)
        reachable[pc] = end, decoded
        if op != "ret":
            todo.append(end)

    parts = []
    previous_end = 0
    for pc, (end, decoded) in sorted(reachable.items()):
        if previous_end > pc or end > size:
            raise ValueError(f"invalid instruction boundaries at symbol offset {pc:#x}")
        if previous_end < pc:
            parts.append(literal(raw[previous_end:pc]))
        parts.append(f"(* +0x{pc:04x} *) Op ({decoded})")
        previous_end = end
    if previous_end < size:
        parts.append(literal(raw[previous_end:]))
    (dest / "Program.v").write_text(
        "From Coq Require Import List ZArith.\n"
        "From Machine Require Import isa.Instructions execution.MaskTrace.\n"
        "Import ListNotations. Open Scope Z_scope.\nDefinition code := [\n"
        + ";\n".join(parts) + "\n].\n")
    return raw
