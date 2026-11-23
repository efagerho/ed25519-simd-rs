"""Replay negative controls against a successfully audited ladder ELF."""
import argparse
from pathlib import Path
import subprocess
import tempfile

from audit import component_flags, read_symbol, write_symbol_bytes


def replace_once(value, old, new):
    if value.count(old) != 1:
        raise ValueError(f"expected one mutation site for {old!r}")
    return value.replace(old, new, 1)


def run_case(directory, audit, name, raw, edit, expect):
    work = directory / name
    work.mkdir()
    ladder = work / "LadderStep"
    ladder.mkdir()
    flags = [*component_flags("ladder_step"), "-Q", "Double4", "Ed25519Simd.Double4",
             "-Q", "CachedAdd", "Ed25519Simd.CachedAdd"]
    for dep in ["machine", "arithmetic", "curve25519", "crate", "Double4", "CachedAdd"]:
        (work / dep).symlink_to(audit / dep)
    for dep in ["PointMode.vo", "Modes.vo", "Callees.vo", "Schedule.vo"]:
        (ladder / dep).symlink_to(audit / "LadderStep" / dep)
    for mod in ["Audit", "Calls", "Execution", "Object"]:
        source = (audit / "LadderStep" / (mod + ".v")).read_text()
        if mod == "Audit" and edit:
            source = replace_once(source, *edit)
        (ladder / (mod + ".v")).write_text(source)
    linked = ladder / "LinkedBytes.v"
    write_symbol_bytes(linked, raw)
    with linked.open("a") as dest:
        for line in (audit / "LadderStep/LinkedBytes.v").read_text().splitlines():
            if "_pc : Z :=" in line:
                dest.write(line + "\n")

    modules = ["LinkedBytes", "Audit", "Calls", "Execution", "Object"]
    if edit:
        # A wrong semantic result must be rejected even when the byte binding succeeds.
        (ladder / "Binding.v").write_text(
            "From Machine Require Import execution.LinkedCalls. From Ed25519Simd.LadderStep Require Import Audit LinkedBytes.\n"
            "Example binds : assemble wrapper_pc program=Some symbol_bytes.\n"
            "Proof. vm_compute. reflexivity. Qed.\n")
        modules.insert(2, "Binding")
    for mod in modules:
        check = subprocess.run(["coqc", *flags, "LadderStep/" + mod + ".v"], cwd=work,
                               capture_output=True, text=True)
        if check.returncode:
            if mod != expect or f'File "./LadderStep/{mod}.v"' not in check.stderr:
                raise RuntimeError(check.stderr)
            print(f"{name}: rejected in {mod}.v")
            return
    if expect:
        raise AssertionError(f"accepted mutation: {name}")


def test(elf, audit):
    wrapper_pc, raw = read_symbol(elf, "ladder_step")
    add_pc, _ = read_symbol(elf, "add_cached")
    double_pc, _ = read_symbol(elf, "double4")
    # First call follows three pushes and three register copies.
    pc = wrapper_pc + 14
    def call(target):
        return b"\xe8" + (target - (pc + 5)).to_bytes(4, "little", signed=True)
    if raw[14:19] != call(double_pc):
        raise ValueError("unexpected first call")
    cases = [
        ("original", raw, None, None),
        ("swap-odd-and-base-in-group-result", raw,
         ("ladder_sum P Odd Base Even", "ladder_sum P Base Odd Even"), "Object"),
        ("redirect-first-call", raw[:14] + call(add_pc) + raw[19:], None, "Object"),
        ("omit-base-t", replace_once(raw, bytes.fromhex("ba01000000b901000000"),
                                     bytes.fromhex("ba00000000b901000000")),
         ("++ affine_setup ++", "++ [Immediate RDX 0; Immediate RCX 1] ++"), "Execution"),
        ("restore-wrong-register", replace_once(raw, bytes.fromhex("415d415c5bc3"),
                                                bytes.fromhex("415c415c5bc3")),
         ("Restore R13; Restore R12", "Restore R12; Restore R12"), "Execution"),
    ]
    with tempfile.TemporaryDirectory() as temp:
        for case in cases:
            run_case(Path(temp), audit, *case)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args()
    test(args.elf.resolve(), args.audit.resolve())
