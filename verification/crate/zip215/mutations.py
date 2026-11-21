"""Require the public ZIP-215 theorem to reject changes to linked wrapper bytes."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from audit import FLAGS, inputs
from elf import executable_offset, symbol_extent

# Original instruction bytes must occur exactly once within their symbol.
CASES = (
    ("omit candidate T", "candidate", "41 b9 01 00 00 00", "41 b9 00 00 00 00"),
    ("ignore input validity", "scatter", "41 20 c2", "41 08 c2"),
    ("flush after seven chunks", "push", "83 f8 08", "83 f8 07"),
    ("accept mismatched second chunk", "check_r", "41 21 c5", "41 09 c5"),
    ("skip unresolved chunk", "flush", "42 80 3c 2c ff 74", "42 80 3c 2c ff 75"),
    ("ignore decoder validity", "decoded", "44 21 e0", "44 09 e0"),
)


def check(elf, audit, work):
    for path in audit.iterdir():
        if path.is_dir() and path.name not in ("Zip215", "sources"):
            (work / path.name).symlink_to(path, target_is_directory=True)
    dest = work / "Zip215"
    shutil.copytree(audit / "Zip215", dest)

    def compile_module(name, reject=False):
        result = subprocess.run(["coqc", *FLAGS, f"Zip215/{name}.v"], cwd=work,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if reject and result.returncode and "Unable to unify" in result.stdout:
            return
        if reject or result.returncode:
            raise AssertionError(f"unexpected result compiling {name}: {result.stdout[-1200:]}")

    for description, suffix, old, new in CASES:
        mutated = work / "mutated"
        shutil.copyfile(elf, mutated)
        pc, size = symbol_extent(elf, "ed25519_simd_zip215_" + suffix)
        original, replacement = bytes.fromhex(old), bytes.fromhex(new)
        with mutated.open("r+b") as f:
            start = executable_offset(f, pc, size)
            f.seek(start)
            data = f.read(size)
            if data.count(original) != 1 or len(original) != len(replacement):
                raise AssertionError(description)
            f.seek(start + data.index(original))
            f.write(replacement)
        _, modules = inputs(mutated, dest)
        for name in (*modules, "Binding", "Audit"):
            compile_module(name)
        compile_module("Object", reject=True)
        print(f"Public ZIP-215 theorem rejected mutation: {description}", flush=True)

    # A mutation of the grouped semantics can keep the bytes identical.
    # The path proof must still reject giving an unchecked byte to scatter.
    source = dest / "Schedule.v"
    original = source.read_text()
    before = "go (full i) false i pair stack writes"
    assert original.count(before) == 1
    source.write_text(original.replace(before, "go (negb (full i)) false i pair stack writes"))
    compile_module("Schedule", reject=True)
    print("Queue proof rejected inverted exact-match semantics", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="zip215-mutations-") as tmp:
        check(args.elf.resolve(), args.audit.resolve(), Path(tmp))
