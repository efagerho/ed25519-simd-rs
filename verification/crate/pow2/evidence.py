"""Retain the exact inputs, proof-check result, and tool versions for a release audit."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

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


def write_evidence(binary, address, raw, work, checks, cases):
    (work / "symbol.bin").write_bytes(raw)
    # Preserve the generator/checker sources as well as the generated Coq terms.
    sources = work / "sources"
    sources.mkdir()
    shutil.copyfile(HERE.parents[2] / "src/wide/avx512ifma/pow2.S", sources / "pow2.S")
    for path in sorted(HERE.glob("*.py")):
        shutil.copyfile(path, sources / path.name)
    shutil.copyfile(HERE.parents[1] / "proof_build.py", sources / "proof_build.py")
    coq_sources = sorted(work.rglob("*.v"))
    (work / "_CoqProject").write_text("-Q machine Machine\n-Q arithmetic ProofArithmetic\n" + "".join(
        str(path.relative_to(work)) + "\n" for path in coq_sources))
    retained = [*coq_sources, *sources.iterdir(), work / "_CoqProject", work / "machine/_CoqProject", work / "arithmetic/_CoqProject",
                work / "pow2.expanded.S", work / "symbol.bin", work / "assumptions.txt", work / "coqchk.log"]
    if cases:
        retained.append(work / cases["path"])
    manifest = {
        "schema_version": 1,
        "theorem": "Object.assembled_symbol_correct : Audit.pow2_contract ObjectBytes.symbol_bytes",
        "elf": {"name": binary.name, "sha256": sha256(binary)},
        "symbol": {"name": "ed25519_simd_pow2_ifma", "address": address, "size": len(raw),
                   "sha256": hashlib.sha256(raw).hexdigest()},
        "proof_checks": checks, "tools": tool_versions(), "cases": cases,
        "files": {str(path.relative_to(work)): sha256(path) for path in sorted(retained)},
    }
    (work / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
