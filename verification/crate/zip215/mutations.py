"""Require the public ZIP-215 theorem to reject changes to linked wrapper bytes."""
import argparse
from pathlib import Path
import shutil
import tempfile

from audit import FLAGS, inputs
from crate.post_hash.check_mutations import compile_module, mutate

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

    def compile_local(name, reject=False):
        compile_module(work, FLAGS, "Zip215", name, reject)

    for description, suffix, old, new in CASES:
        mutated = work / "mutated"
        mutate(elf, mutated, "ed25519_simd_zip215_" + suffix, old, new)
        _, modules = inputs(mutated, dest)
        for name in (*modules, "Binding", "Audit"):
            compile_local(name)
        compile_local("Object", reject=True)
        print(f"Public ZIP-215 theorem rejected mutation: {description}", flush=True)

    # A mutation of the grouped semantics can keep the bytes identical.
    # The path proof must still reject giving an unchecked byte to scatter.
    source = dest / "Schedule.v"
    original = source.read_text()
    before = "go (full i) false i pair stack writes"
    assert original.count(before) == 1
    source.write_text(original.replace(before, "go (negb (full i)) false i pair stack writes"))
    compile_local("Schedule", reject=True)
    print("Queue proof rejected inverted exact-match semantics", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="zip215-mutations-") as tmp:
        check(args.elf.resolve(), args.audit.resolve(), Path(tmp))
