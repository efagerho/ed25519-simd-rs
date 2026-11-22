"""Patch one instruction in a scratch ELF and distinguish proof failure from tool errors."""
import shutil
import subprocess

from elf import executable_offset, symbol_extent


def compile_module(work, flags, namespace, name, reject=False, diagnostic="Unable to unify"):
    result = subprocess.run(["coqc", *flags, f"{namespace}/{name}.v"], cwd=work,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if reject and result.returncode and diagnostic in result.stdout:
        return
    if reject or result.returncode:
        raise AssertionError(f"unexpected result compiling {name}: {result.stdout[-1200:]}")


def mutate(elf, mutated, symbol, old, new):
    shutil.copyfile(elf, mutated)
    pc, size = symbol_extent(elf, symbol)
    original, replacement = bytes.fromhex(old), bytes.fromhex(new)
    with mutated.open("r+b") as f:
        start = executable_offset(f, pc, size)
        f.seek(start)
        data = f.read(size)
        if data.count(original) != 1 or len(original) != len(replacement):
            raise AssertionError(f"expected one patch site in {symbol}: {old}")
        f.seek(start + data.index(original))
        f.write(replacement)
