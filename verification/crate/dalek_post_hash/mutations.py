"""Recheck the auditor-facing Dalek theorem on corrupted copies of the release ELF."""
import argparse
from pathlib import Path
import shutil
import tempfile

from audit import ENTRIES, FLAGS
from crate.post_hash.build import symbol_inputs
from crate.post_hash.check_mutations import compile_module, mutate

CASES = (
    ("wrong ladder output mode", "Candidate", "45 31 c9", "45 89 c9"),
    ("screen only seven encodings", "Push", "4c 8d 9a 00 01 00 00", "4c 8d 9a e0 00 00 00"),
    ("flush at seven chunks", "Push", "83 f8 08", "83 f8 07"),
    ("keep stale queue count", "Flush", "48 c7 87 80 32 00 00 00 00 00 00", "48 c7 87 80 32 00 00 01 00 00 00"),
    ("shift past one lane instead of one chunk", "Flush", "49 c1 ee 08", "49 c1 ee 01"),
    ("accept noncanonical decoded Y", "Decoded", "c5 f8 93 c2 f7 d0", "c5 f8 93 c2 90 90"),
    ("ignore decoded X mismatch", "Decoded", "44 21 e0", "44 09 e0"),
    ("undersize candidate stack frame", "Decoded", "48 81 ec 00 05 00 00", "48 81 ec c0 04 00 00"),
    ("gather wrong cached digit", "Filter", "91 3c 25 00 0a 00 00", "91 3c 25 60 09 00 00"),
    ("reverse the weak-key mask", "Filter", "c5 f9 df c1", "c5 f9 db c1"),
    ("ignore eligibility during scatter", "Scatter", "41 20 c2", "41 08 c2"),
)


def check(elf, audit, work):
    ns = "DalekPostHash"
    for path in audit.iterdir():
        if path.is_dir() and path.name not in (ns, "sources"):
            (work / path.name).symlink_to(path, target_is_directory=True)
    dest = work / ns
    shutil.copytree(audit / ns, dest)
    def compile_local(name, **kwargs):
        compile_module(work, FLAGS, ns, name, **kwargs)

    for description, label, old, new in CASES:
        binary = work / "mutated"
        mutate(elf, binary, ENTRIES[label], old, new)
        _, modules = symbol_inputs(binary, dest, ENTRIES)
        for name in (*modules, "Binding", "Audit"):
            compile_local(name)
        compile_local("Object", reject=True)
        print(f"Public Dalek theorem rejected mutation: {description}", flush=True)

    # Keep the release bytes intact. Reversing the public weak-key predicate
    # must break the equivalence in the proof of the decoded output.
    _, modules = symbol_inputs(elf, dest, ENTRIES)
    for name in (*modules, "Binding"):
        compile_local(name)
    source = dest / "Audit.v"
    original = source.read_text()
    expected = "multiple 8 (key b j) <> identity /\\"
    assert original.count(expected) == 1
    source.write_text(original.replace(expected, expected.replace("<>", "=")))
    compile_local("Audit")
    compile_local("Object", reject=True, diagnostic="tauto failed")
    print("Public Dalek theorem rejected the inverted weak-key specification", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="dalek-post-hash-mutations-") as tmp:
        check(args.elf.resolve(), args.audit.resolve(), Path(tmp))
