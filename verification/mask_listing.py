"""Lift reachable instructions. Coq re-encodes them against the complete ELF symbol."""
import re
import subprocess
from elf import symbol_bytes, symbol_extent

VECTOR_OPS = {
    "vmovdqa64": "Copy", "vpaddq": "Add", "vpsubq": "Sub", "vpmullq": "Mul",
    "vpandq": "And", "vpxorq": "Xor", "vpsrlq": "Shr", "vpsllq": "Shl",
    "vpmadd52luq": "Madd false", "vpmadd52huq": "Madd true",
}
FIXED = {
    ("push", "rbp"): "PushBP", ("pop", "rbp"): "PopBP",
    ("mov", "rbp,rsp"): "SetBP", ("mov", "rsp,rbp"): "RestoreSP",
    ("and", "rsp,0xffffffffffffffc0"): "AlignSP", ("vzeroupper", ""): "VZeroUpper",
    ("xor", "eax,eax"): "ZeroEax",
    ("ret", ""): "Return",
}


def address(operand):
    match = re.fullmatch(r"\[(rdi|rsi|rsp|rip)([+-]0x[0-9a-f]+)?\]", operand)
    if not match:
        raise ValueError(f"unsupported memory operand {operand}")
    disp = int(match[2] or "0", 0)
    return match[1], disp - (1 << 64) if disp >= 1 << 63 else disp


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
    if op == "kortestw" and dst == src:
        return f"TestMask {register(dst)}"
    if op == "vpminuq":
        return "MinUnsigned " + " ".join(str(register(v)) for v in operands)
    if op in ("vpmullq", "vpcmpltuq") and operands[2].startswith("QWORD BCST "):
        base, disp = address(operands[2][len("QWORD BCST "):])
        if base != "rip":
            raise ValueError(f"expected RIP-relative qword broadcast: {args}")
        kind = "RipMul" if op == "vpmullq" else "RipLessUnsigned"
        return f"{kind} {register(dst)} {register(src)} ({disp})"
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


def instructions(binary, name):
    dump = subprocess.check_output(["objdump", "-dz", "-Mintel", "--insn-width=16",
                                    "--disassemble=" + name, binary], text=True)
    rows = {}
    for line in dump.splitlines():
        match = re.fullmatch(r"\s*([0-9a-f]+):\s*((?:[0-9a-f]{2} )+)\s*(\S+)(?:\s+(.*))?", line)
        if match:
            pc = int(match[1], 16)
            rows[pc] = (pc + len(bytes.fromhex(match[2])), match[3],
                        (match[4] or "").partition("#")[0].strip())
    return rows


def linked_program(binary, symbols, dest):
    """Follow control transfers from the first entry using the actual linked addresses."""
    rows = {}
    regions = []
    for name, definition in symbols:
        start, size = symbol_extent(binary, name)
        regions.append((name, start, symbol_bytes(binary, start, size), definition))
        rows.update(instructions(binary, name))

    reachable = {}
    todo = [regions[0][1]]
    transfers = {"je": "Je", "jne": "Jne8", "call": "Call", "jmp": "Jump"}
    while todo:
        pc = todo.pop()
        if pc in reachable:
            continue
        if pc not in rows:
            raise ValueError(f"no instruction at reachable address {pc:#x}")
        end, op, args = rows[pc]
        if op in transfers:
            target = int(args.split()[0], 16)
            todo.append(target)
            decoded = f"{transfers[op]} ({target-end})"
        else:
            decoded = instruction(op, args)
        reachable[pc] = end, decoded
        if op not in ("ret", "jmp"):
            todo.append(end)

    definitions = []
    for name, start, raw, definition in regions:
        parts = []
        last = start
        for pc, (end, decoded) in sorted(reachable.items()):
            if not start <= pc < start + len(raw):
                continue
            if pc < last or end > start + len(raw):
                raise ValueError(f"invalid instruction boundary in {name} at {pc:#x}")
            if last < pc:
                parts.append(literal(raw[last-start:pc-start]))
            parts.append(f"(* +0x{pc-start:04x} *) Op ({decoded})")
            last = end
        if last < start + len(raw):
            parts.append(literal(raw[last-start:]))
        definitions.append(f"Definition {definition} := [\n" + ";\n".join(parts) + "\n].\n")
    (dest / "Program.v").write_text(
        "From Coq Require Import List ZArith.\n"
        "From Machine Require Import isa.Instructions execution.MaskTrace.\n"
        "Import ListNotations. Open Scope Z_scope.\n" + "".join(definitions))
    return [(name, start, raw) for name, start, raw, _ in regions]
