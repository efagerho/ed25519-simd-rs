"""Link the deferred-carry audit fixture without changing the checkout."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ASM = Path("src/wide/avx512ifma")
ROUTINES = ("double4", "add_cached", "stage_round", "ladder_step", "mul_s_base_minus_k_public")


def build(output):
    with tempfile.TemporaryDirectory(prefix="carry-assembly-") as directory:
        work = Path(directory)
        (work / ASM).mkdir(parents=True)
        for name in ROUTINES:
            shutil.copyfile(ROOT / ASM / (name + ".S"), work / ASM / (name + ".S"))
        subprocess.run(["git", "apply", str(HERE / "private-entries.patch")], cwd=work, check=True)
        product = (ROOT / ASM / "fe51_product.inc").read_text()
        objects = []
        for name in ROUTINES:
            source = (work / ASM / (name + ".S")).read_text()
            if name in ("double4", "add_cached"):
                source = product + "\n" + source
            obj = work / (name + ".o")
            subprocess.run([os.getenv("LLVM_MC", "llvm-mc"), "-triple=x86_64-pc-linux-gnu",
                            "-x86-asm-syntax=intel", "-filetype=obj", "-o", obj],
                           input=source, text=True, check=True)
            objects.append(obj)
        subprocess.run(["ld", "-e", "ed25519_simd_mul_s_base_minus_k_public", "-o",
                        work / "fixture", *objects], check=True)
        with output.open("xb") as dest, (work / "fixture").open("rb") as source:
            shutil.copyfileobj(source, dest)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    build(parser.parse_args().output)
