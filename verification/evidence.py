"""Retain the exact inputs, proof-check result, and tool versions for a release audit."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from proof_build import write_project

HERE = Path(__file__).resolve().parent


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tool_versions():
    commands = {"coqc": ["coqc", "--version"], "coqchk": ["coqchk", "-v"],
                "llvm-mc": [os.getenv("LLVM_MC", "llvm-mc"), "--version"],
                **{name: [name, "--version"] for name in ("nm", "objcopy", "objdump")}}
    versions = {name: {"command": command,
                       "version": subprocess.check_output(command, text=True).strip()}
                for name, command in commands.items()}
    versions["python"] = {"command": [sys.executable], "version": sys.version}
    return versions


def write_evidence(binary, work, component, checks, symbols, sources, flags, cases=None):
    """Retain one checked declaration and all of its linked symbol inputs."""
    coq_sources = sorted(work.rglob("*.v"))
    dest = work / "sources"
    dest.mkdir()
    for path in sources:
        shutil.copyfile(path, dest / path.name)
    for path in [HERE / "proof_build.py", HERE / "elf.py", Path(__file__)]:
        shutil.copyfile(path, dest / path.name)
    if component in ("torsion", "small_order", "decompress_r", "dalek_recompress", "zip215", "dalek_post_hash"):
        shutil.copyfile(HERE / "mask_listing.py", dest / "mask_listing.py")
    dependencies = {component} if component in ("small_order", "stage_round") else {"pow2", component}
    if component == "dalek_recompress":
        dependencies = {component, "decompress_r", "small_order"}
    if component in ("zip215", "dalek_post_hash"):
        dependencies.add("post_hash")
        dependencies.update(("radix16", "scalar", "full_ladder", "ladder_step", "stage_round",
                             "double4", "cached_add", "decompress_r", "dalek_recompress",
                             "small_order"))
    if component == "zip215":
        dependencies.add("torsion")
    if component == "full_ladder":
        dependencies.update(("ladder_step", "stage_round"))
    if component in ("ladder_step", "full_ladder"):
        dependencies.update(("double4", "cached_add"))
    if component == "radix16":
        dependencies.add("scalar")
    for name in sorted(dependencies):
        directory = dest if component == "pow2" else dest / name
        directory.mkdir(exist_ok=True)
        for path in (HERE / "crate" / name).glob("*.py"):
            shutil.copyfile(path, directory / path.name)

    write_project(work, flags, coq_sources)
    retained = [*coq_sources, *(p for p in dest.rglob("*") if p.is_file()),
                *work.rglob("_CoqProject"), *work.rglob("*.expanded.S"),
                work / "assumptions.txt", work / "coqchk.log"]
    metadata = []
    for index, (name, address, raw) in enumerate(symbols):
        path = work / ("symbol.bin" if index == 0 else name + ".bin")
        path.write_bytes(raw)
        retained.append(path)
        metadata.append({"name": name, "address": address, "size": len(raw),
                         "path": path.name, "sha256": sha256(path)})
    if cases:
        retained.append(work / cases["path"])
    manifest = {
        "schema_version": 1, "theorem": checks["theorem"],
        "elf": {"name": binary.name, "sha256": sha256(binary)},
        "symbol": metadata[0], "symbols": metadata,
        "proof_checks": checks, "tools": tool_versions(), "cases": cases,
        "files": {str(p.relative_to(work)): sha256(p) for p in sorted(retained)},
    }
    (work / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
