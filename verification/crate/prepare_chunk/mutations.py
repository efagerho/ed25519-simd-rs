"""Recompile the public statement against independently damaged copies of the ELF."""
import argparse
from pathlib import Path
import shutil
import tempfile

from audit import ENTRIES, FLAGS
from crate.post_hash.build import symbol_inputs
from crate.post_hash.check_mutations import compile_module, mutate

CASES = (
    ("start S one byte early", "Common", "b8 20 00 00 00", "b8 1f 00 00 00"),
    ("halve the stack allocation", "Common", "48 83 ec 40", "48 83 ec 20"),
    ("drop the last two encoding pairs", "Common", "81 f9 00 01 00 00", "81 f9 c0 00 00 00"),
    ("decode only the keys", "Common", "ba 02 00 00 00", "ba 01 00 00 00"),
    ("combine S and A with OR", "Common", "45 21 fe", "45 09 fe"),
    ("ignore R eligibility", "Common", "41 21 c6", "90 90 90"),
    ("shift the R mask by seven", "Common", "c1 e8 08", "c1 e8 07"),
    ("select the next lane's table", "Common", "00 0e a0 18", "a0 18 a0 18"),
    ("emit 255 for true", "Common", "62 f2 7d 48 1c c0", "90 90 90 90 90 90"),
    ("skip weak-key filtering on success", "Strict", "85 c0 74 16", "85 c0 75 16"),
    ("invert the strict return", "Strict", "0f 95 c0", "0f 94 c0"),
)


def check(elf, audit, work):
    ns = "PrepareChunk"
    for path in audit.iterdir():
        if path.is_dir() and path.name not in (ns, "sources"):
            (work / path.name).symlink_to(path)
    dest = work / ns
    shutil.copytree(audit / ns, dest)
    symbols, _ = symbol_inputs(elf, dest, ENTRIES)
    for name, _, raw in symbols:
        path = "symbol.bin" if name == ENTRIES["Common"] else name + ".bin"
        if raw != (audit / path).read_bytes():
            raise ValueError(f"{name} differs from the certified ELF")
    for description, label, old, new in CASES:
        binary = work / "mutated.elf"
        mutate(elf, binary, ENTRIES[label], old, new)
        _, modules = symbol_inputs(binary, dest, ENTRIES)
        for name in (*modules, "Audit"):
            compile_module(work, FLAGS, ns, name)
        compile_module(work, FLAGS, ns, "Object", reject=True)
        print(f"Public preparation theorem rejected mutation: {description}", flush=True)

    # Exercise the meaning independently of the byte comparison. Keep both
    # ELF images intact and invert the public eligibility-byte specification.
    _, modules = symbol_inputs(elf, dest, ENTRIES)
    for name in modules:
        compile_module(work, FLAGS, ns, name)
    source = dest / "Audit.v"
    expected = "m (selected p+64+Z.of_nat j)=1 <-> accepts mode p j"
    original = source.read_text()
    if original.count(expected) != 1:
        raise ValueError("missing public eligibility-byte specification")
    source.write_text(original.replace(expected, expected.replace("=1", "=0")))
    compile_module(work, FLAGS, ns, "Audit")
    compile_module(work, FLAGS, ns, "Object", reject=True, diagnostic="while it is expected to have type")
    print("Public preparation theorem rejected the inverted eligibility specification", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="prepare-chunk-mutations-") as temp:
        check(args.elf.resolve(), args.audit.resolve(), Path(temp))
