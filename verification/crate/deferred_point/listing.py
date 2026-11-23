"""Decode both entries of a point routine into the shared x86 block model."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from elf import symbol_bytes, symbol_extent
from mask_listing import instructions
from proof_build import write_symbol_bytes

DOUBLE = ("ed25519_simd_double4_for_add_ifma", "ed25519_simd_double4_ifma")
ADD = ("ed25519_simd_add_affine_for_add_ifma", "ed25519_simd_add_cached_ifma")
TRANSFERS = {"jmp", "je", "jne", "call", "ret", "push", "pop"}


def point_program(elf, dest, names, module):
    symbols, rows = [], {}
    for name in names:
        start, size = symbol_extent(elf, name)
        symbols.append((name, start, symbol_bytes(elf, start, size)))
        rows.update(instructions(elf, name))
    _, base, stub = symbols[0]
    _, public, body = symbols[1]
    if public != base + len(stub):
        raise ValueError("point entries must be contiguous")
    image = stub + body
    write_symbol_bytes(dest / (module + "Bytes.v"), image)
    with (dest / (module + "Bytes.v")).open("a") as out:
        out.write(f"Definition private_pc := {base}%Z.\nDefinition public_pc := {public}%Z.\n")

    leaders = {base, public}
    for end, op, args in rows.values():
        if op in TRANSFERS:
            leaders.add(end)
            if op in {"jmp", "je", "jne", "call"}:
                leaders.add(int(args.split()[0], 16))

    def vector(op, args):
        return (op.startswith("v") and op not in ("vzeroupper", "vpbroadcastq") and
                not (op == "vmovdqu64" and args.startswith("ZMMWORD")))

    parts = []
    pc = base
    while pc < base + len(image):
        start = pc
        _, op, args = rows[pc]
        if op == "nop":
            pc = rows[pc][0]
            parts.append("LiteralPadding [" + ";".join(map(str, image[start-base:pc-base])) + "]")
            continue
        vec = vector(op, args)
        ops = []
        ending = "FallThrough"
        while True:
            end, op, args = rows[pc]
            if op in TRANSFERS:
                if op in ("ret", "push", "pop"):
                    if op != "ret" and args != "rbp":
                        raise ValueError(f"unsupported frame operation {op} {args}")
                    ending = {"ret": "Return", "push": "PushFrame", "pop": "PopFrame"}[op]
                else:
                    target = int(args.split()[0], 16) - base
                    constructor = {"je": "JeTo", "jne": "JneTo", "call": "CallTo",
                                   "jmp": "JumpTo " + ("true" if end-pc == 2 else "false")}[op]
                    ending = f"({constructor} {target})"
                pc = end
                break
            args = args.lower().replace("0xffffffffffffffc0", "-64")
            ops.append(f"(* +0x{pc-base:x} *) {op} {args}")
            pc = end
            if pc in leaders or pc not in rows or rows[pc][1] == "nop":
                break
            if rows[pc][1] not in TRANSFERS and vector(rows[pc][1], rows[pc][2]) != vec:
                break
        section, notation = ("VectorBlock", "vecs") if vec else ("ScalarBlock", "ops")
        code = notation + "[\n  " + ";\n  ".join(ops) + "\n]" if ops else "[]"
        parts.append(f"{section} {start-base} {code} {ending}")
    (dest / (module + ".v")).write_text(
        "From Coq Require Import ZArith List.\nFrom Machine Require Import isa.IntelSyntax.\n"
        "Import ListNotations. Open Scope Z_scope.\nDefinition program := Eval vm_compute in assemble [\n"
        + ";\n".join(parts) + "].\n")
    return symbols
