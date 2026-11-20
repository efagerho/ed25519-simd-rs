"""Generate the executable Coq listing from the assembly used by Rust."""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from elf import SYMBOL, disassemble, require

SOURCE = Path(__file__).resolve().parents[3] / "src/wide/avx512ifma/pow2.S"


def mc(*args, **kwargs):
    return subprocess.run([os.getenv("LLVM_MC", "llvm-mc"), "-triple=x86_64-pc-linux-gnu",
                           "-x86-asm-syntax=intel", *args], check=True, **kwargs)


def assemble(source, work, name, symbol=SYMBOL):
    obj, raw = work / (name + ".o"), work / (name + ".bin")
    mc("-filetype=obj", "-o", obj, source)
    reloc = subprocess.check_output(["objdump", "-r", "-j", ".text", obj], text=True)
    if "RELOCATION RECORDS" in reloc:
        raise ValueError(f"{source}: expected a relocation-free text section")
    subprocess.run(["objcopy", "-O", "binary", "-j", ".text", obj, raw], check=True)
    data = raw.read_bytes()
    nm = subprocess.check_output(["nm", "-S", "--defined-only", obj], text=True)
    m = re.search(rf"^([0-9a-f]+) ([0-9a-f]+) T {re.escape(symbol)}$", nm, re.M)
    if not m or int(m[1], 16) != 0 or int(m[2], 16) != len(data):
        raise ValueError(f"{source}: expected exactly one symbol spanning .text")
    return data


def block_listing(code, rows, labels, padding):
    """Group expanded Intel lines at branch targets and continuations."""
    target_names = {}
    leaders = {0}
    for pc, asm in rows.items():
        nxt, op, args = code[pc]
        if op in ("call", "jne"):
            target = int(args[0], 16)
            mnemonic, _, label = asm.partition(" ")
            require(mnemonic == op and labels.get(label) == target,
                    f"branch label disagrees with target at +0x{pc:x}")
            target_names[target] = label
            leaders.update((nxt, target))

    def annotated(pc):
        return f"    (* +0x{pc:04x} *) {rows[pc]}"

    sections = []
    pc = 0
    while pc in rows or pc in padding:
        if pc in padding:
            octets = "; ".join(f"0x{b:02x}" for b in padding[pc])
            sections.append(f"LiteralPadding [{octets}]")
            pc += len(padding[pc])
            continue
        start = pc
        body = []
        last = None
        while True:
            insn_pc = pc
            pc, op, _ = code[pc]
            if op in ("call", "jne", "ret"):
                last = insn_pc
                break
            body.append(annotated(insn_pc))
            if pc in leaders or pc in padding:
                break
        vector = start in (labels.get(".Lsquare"), labels.get(".Lmultiply"))
        kind = "VectorBlock" if vector else "ScalarBlock"
        entry = f"label[ {target_names[start]} ]" if start in target_names else f"0x{start:04x}"
        ops = "[]"
        if body:
            opener = "vecs[" if vector else "ops["
            ops = opener + "\n" + ";\n".join(body) + "\n  ]"
        ending = f"ends[\n{annotated(last)}\n  ]" if last is not None else "FallThrough"
        sections.append(f"{kind} {entry} {ops} {ending}")

    bindings = [f"Local Notation \"'{name}'\" := (0x{pc:04x}%Z) (in custom intel_label at level 0)."
                for name, pc in labels.items() if pc in target_names]
    return ("(* Generated from pow2.S. Offsets are relative to the symbol. *)\n"
            "From Coq Require Import List ZArith.\n"
            "From Machine Require Import isa.IntelSyntax.\n"
            "Import ListNotations. Open Scope Z_scope.\n\n"
            + "\n".join(bindings) + "\n\nDefinition pow2_program := assemble [\n  "
            + ";\n  ".join(sections) + "].\n")


def write_listings(work, assembly, code, raw):
    labels, rows, padding = {}, {}, {}
    lines = [".intel_syntax noprefix", "// Generated from pow2.S. Offsets are relative to the symbol."]
    pc = 0
    # Map each expanded instruction to its assembled offset. Only alignment
    # directives may introduce bytes between instructions.
    for line in assembly.splitlines():
        asm = " ".join(line.split())
        if not asm:
            continue
        start = pc
        if asm.endswith(":"):
            labels[asm[:-1]] = pc
        elif align := re.fullmatch(r"\.p2align ([0-9]+)(?:, (?:0x[0-9a-fA-F]+|[0-9]+))?", asm):
            length = -pc % (1 << int(align[1]))
            if length:
                require(pc + length <= len(raw), "alignment exceeds symbol")
                padding[pc] = raw[pc:pc + length]
                pc += length
        elif asm.split()[0] not in (".text", ".globl", ".hidden", ".type", ".size"):
            require(pc in code and not asm.startswith("."), f"unexpected assembly at +0x{pc:x}: {asm}")
            rows[pc] = asm
            pc = code[pc][0]
        if start < pc:
            lines.append(f"    {asm:<49} // +{start:04x} {raw[start:pc].hex(' ')}")
        else:
            lines.append(asm)
    require(pc == len(raw), "expansion does not span symbol")
    (work / "pow2.expanded.S").write_text("\n".join(lines) + "\n")
    (work / "Program.v").write_text(block_listing(code, rows, labels, padding))


def generate(work):
    """Write Program.v and the expanded assembly, and return the assembled bytes."""
    with tempfile.TemporaryDirectory(dir=work) as tmp:
        objects = Path(tmp)
        raw = assemble(SOURCE, objects, "macro")
        base, code = disassemble(objects / "macro.o")
        require(base == 0, "unexpected symbol offset")
        assembly = mc("-filetype=asm", "--output-asm-variant=1", SOURCE,
                      capture_output=True, text=True).stdout
        write_listings(work, assembly, code, raw)
        require(assemble(work / "pow2.expanded.S", objects, "expanded") == raw,
                "macro expansion changed the symbol bytes")
    return raw


if __name__ == "__main__":
    dest = Path(sys.argv[1])
    dest.mkdir(parents=True, exist_ok=False)
    generate(dest)
