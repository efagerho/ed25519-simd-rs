"""Emit Rust's double4 include from bytes certified by the complete Coq theorem."""
from pathlib import Path
import sys
import tempfile
from certificate import certify
from listing import SYMBOL, generate


def emit_for_rust(outdir):
    with tempfile.TemporaryDirectory(dir=outdir) as temp:
        data = generate(Path(temp))
        certify(data, Path(temp))
    lines = [".text", ".p2align 4", f".globl {SYMBOL}", f".hidden {SYMBOL}",
             f".type {SYMBOL},@function", SYMBOL + ":"]
    lines.extend(".byte " + ",".join(f"0x{x:02x}" for x in data[i:i+16])
                 for i in range(0, len(data), 16))
    lines.append(f".size {SYMBOL}, .-{SYMBOL}")
    (outdir / "double4-checked.S").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    emit_for_rust(Path(sys.argv[1]))
