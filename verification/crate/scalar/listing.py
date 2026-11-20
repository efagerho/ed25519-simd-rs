"""Expand reduce.S into readable, byte-bound executable Coq instructions."""
import re
import sys
import tempfile
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[1] / "pow2"))
from disassembly import disassemble, require
from generate_listing import assemble, mc

SYMBOL = "ed25519_simd_scalar_reduce_ifma"
SOURCE = Path(__file__).resolve().parents[3] / "src/scalar/reduce.S"


def generate(work):
    with tempfile.TemporaryDirectory(dir=work) as temp:
        objects = Path(temp)
        raw = assemble(SOURCE, objects, "macro", SYMBOL)
        _, code = disassemble(objects / "macro.o", SYMBOL)
        expanded = mc("-filetype=asm", "--output-asm-variant=1", SOURCE,
                      capture_output=True, text=True).stdout
        labels, rows, padding = {}, {}, {}
        pc = 0
        lines = [".intel_syntax noprefix"]
        for line in expanded.splitlines():
            asm = " ".join(line.split())
            if not asm:
                continue
            start = pc
            if asm.endswith(":"):
                labels[asm[:-1]] = pc
            elif align := re.fullmatch(r"\.p2align ([0-9]+)(?:, (?:0x[0-9a-fA-F]+|[0-9]+))?", asm):
                size = -pc % (1 << int(align[1]))
                if size:
                    padding[pc] = raw[pc:pc+size]
                    pc += size
            elif asm.split()[0] not in (".text", ".globl", ".hidden", ".type", ".size"):
                require(pc in code and not asm.startswith("."), f"unexpected assembly at {pc}: {asm}")
                rows[pc] = asm
                pc = code[pc][0]
            lines.append(f"    {asm:<52} // +{start:04x} {raw[start:pc].hex(' ')}" if start < pc else asm)
        require(pc == len(raw), "expansion does not span symbol")
        (work / "reduce.expanded.S").write_text("\n".join(lines)+"\n")
        require(assemble(work / "reduce.expanded.S", objects, "expanded", SYMBOL) == raw,
                "macro expansion changed symbol bytes")

    leaders = set(labels.values())
    for pc, asm in rows.items():
        nxt, op, args = code[pc]
        if op in ("call", "jne"):
            label = asm.split()[1]
            require(labels.get(label) == int(args[0], 16), "branch label disagrees with bytes")
            leaders.add(nxt)
        if op in ("push", "pop", "ret"):
            leaders.add(nxt)

    def vector(pc):
        asm = rows[pc]
        op = asm.split()[0]
        return op.startswith("v") and op not in ("vzeroupper", "vpbroadcastq") and not (
            op == "vmovdqu64" and asm.startswith("vmovdqu64 zmmword"))

    sections = []
    pc = 0
    while pc < len(raw):
        if pc in padding:
            sections.append("LiteralPadding [" + ";".join(map(str, padding[pc])) + "]")
            pc += len(padding[pc])
            continue
        start, is_vector, body, ending = pc, vector(pc), [], "FallThrough"
        while True:
            nxt, op, _ = code[pc]
            annotation = f"    (* +0x{pc:04x} *) {rows[pc]}"
            if op in ("call", "jne", "ret", "push", "pop"):
                ending = "ends[ " + rows[pc] + " ]"
                pc = nxt
                break
            body.append(annotation)
            pc = nxt
            if pc not in rows or pc in leaders or vector(pc) != is_vector:
                break
        kind, syntax = ("VectorBlock", "vecs") if is_vector else ("ScalarBlock", "ops")
        ops = syntax + "[\n" + ";\n".join(body) + "\n  ]" if body else "[]"
        sections.append(f"{kind} 0x{start:04x} {ops} {ending}")
    bindings = [f'Local Notation "\'{name}\'" := (0x{offset:04x}%Z) (in custom intel_label at level 0).'
                for name, offset in labels.items() if name.startswith(".L")]
    (work / "Program.v").write_text(
        "(* Generated from reduce.S; checked against the linked symbol bytes. *)\n"
        "From Coq Require Import List ZArith.\nFrom Machine Require Import isa.IntelSyntax.\n"
        "Import ListNotations. Open Scope Z_scope.\n" + "\n".join(bindings) +
        "\nDefinition scalar_program := Eval vm_compute in assemble [\n  " + ";\n  ".join(sections) + "].\n\n")
    return raw


if __name__ == "__main__":
    dest = Path(sys.argv[1])
    dest.mkdir(parents=True, exist_ok=False)
    generate(dest)
