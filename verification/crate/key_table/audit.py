"""Check the public-key table builder and its three linked helper symbols."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from crate.cached_add import certificate, listing
from crate.decompress_r import audit as decoder
from crate.post_hash.build import load_callees, symbol_inputs
from evidence import write_evidence
from proof_build import MASK_PROJECTS, check_object, compile_libraries, compile_object, component_flags, write_project

ENTRY = "ed25519_simd_build_key_tables"
FLAGS = component_flags("key_table") + ["-Q", "CachedAdd", "Ed25519Simd.CachedAdd",
                                       "-Q", "Decode", "Ed25519Simd.Decode"]


def build_project(work):
    sources = sorted(path for ns in ("KeyTable", "Decode") for path in (work / ns).glob("*.v"))
    write_project(work, FLAGS, sources)
    subprocess.run(["coq_makefile", "-f", "_CoqProject", "-o", "Makefile"], cwd=work, check=True)


def replay(elf, work, dependencies):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work, projects=MASK_PROJECTS)
    dest = work / "KeyTable"
    dest.mkdir()
    linked, _ = symbol_inputs(elf, dest, {"Object": ENTRY, "Cached": listing.SYMBOL})
    cached = linked[1][2]
    if dependencies:
        load_callees(elf, work, dependencies, {"full_ladder": ("CachedAdd",)}, {})
    else:
        dest = work / "CachedAdd"
        dest.mkdir()
        if listing.generate(dest) != cached:
            raise ValueError("cached addition differs from the linked symbol")
        compile_object(cached, dest, certificate.proof_sources(),
                       certificate.HERE / "coq/Object.v", component_flags("cached_add", ".", Path("..")))
    (work / "Decode").mkdir()
    helpers = decoder.extract(elf, work / "Decode")
    for name in ("Kernels", "Power", "Image", "Scale", "Decode", "Glue", *decoder.NATIVE_MODULES):
        shutil.copyfile(decoder.HERE / "coq" / (name + ".v"), work / "Decode" / (name + ".v"))
    shutil.copytree(HERE / "coq", work / "KeyTable", dirs_exist_ok=True)
    build_project(work)
    subprocess.run(["make", "-s", "-j4", "KeyTable/Object.vo"], cwd=work, check=True)
    checks = check_object(work, FLAGS, "key_table")
    asm = listing.SOURCE.parent
    write_evidence(elf, work, "key_table", checks, [linked[0], *helpers, linked[1]],
                   [asm / name for name in ("key_table.S", "add_cached.S", "fe51_product.inc", "decompress_r.S",
                                            "torsion.S", "point_encoding.inc", "pow22523.inc")], FLAGS)
    print(f"Checked {checks['theorem']} against {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--dependencies", type=Path, help="reuse the full-ladder audit for this ELF")
    args = parser.parse_args()
    replay(args.elf.resolve(), args.output.resolve(), args.dependencies)
