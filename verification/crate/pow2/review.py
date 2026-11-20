"""Build Rust's assembly include from the bytes certified by Coq."""
from pathlib import Path
import sys
import tempfile

from certify import certify
from disassembly import SYMBOL
from generate_listing import generate


def emit_for_rust(outdir):
    with tempfile.TemporaryDirectory(dir=outdir) as tmp:
        data = generate(Path(tmp))
        certify(data, Path(tmp))
    # Assemble only literal bytes after validation. Internal calls are PC-relative
    # and the object check above disallows relocations in the symbol.
    lines = [".text", ".p2align 4", f".globl {SYMBOL}", f".hidden {SYMBOL}",
             f".type {SYMBOL},@function", SYMBOL + ":"]
    for i in range(0, len(data), 16):
        lines.append(".byte " + ",".join(f"0x{x:02x}" for x in data[i:i+16]))
    lines.append(f".size {SYMBOL}, .-{SYMBOL}")
    (outdir / "pow2-checked.S").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    emit_for_rust(Path(sys.argv[1]))
