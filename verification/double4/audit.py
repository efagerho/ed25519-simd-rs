"""Replay the complete double4 certificate against a linked ELF symbol."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

from certificate import certify
from listing import SYMBOL, SOURCE, generate
from coq_proof import export_cases, symbol_bytes
from elf import symbol_extent
from evidence import sha256, tool_versions

HERE = Path(__file__).resolve().parent


def write_evidence(binary, address, raw, work, checks, cases):
    (work / "symbol.bin").write_bytes(raw)
    sources = work / "sources"
    sources.mkdir()
    shutil.copyfile(SOURCE, sources / SOURCE.name)
    for name, directory in (("double4", HERE), ("pow2", HERE.parent / "pow2")):
        (sources / name).mkdir()
        for path in sorted(directory.glob("*.py")):
            shutil.copyfile(path, sources / name / path.name)
    shutil.copyfile(HERE.parent / "proof_build.py", sources / "proof_build.py")
    coq_sources = sorted(work.rglob("*.v"))
    (work / "_CoqProject").write_text("-Q machine Machine\n-Q arithmetic ProofArithmetic\n" + "".join(
        str(path.relative_to(work)) + "\n" for path in coq_sources))
    retained = [*coq_sources, *(p for p in sources.rglob("*") if p.is_file()),
                work / "_CoqProject", work / "machine/_CoqProject", work / "arithmetic/_CoqProject", work / "double4.expanded.S",
                work / "symbol.bin", work / "assumptions.txt", work / "coqchk.log"]
    if cases:
        retained.append(work / cases["path"])
    manifest = {
        "schema_version": 1,
        "theorem": "Object.assembled_double4_correct : Audit.double4_contract ObjectBytes.symbol_bytes",
        "elf": {"name": binary.name, "sha256": sha256(binary)},
        "symbol": {"name": SYMBOL, "address": address, "size": len(raw),
                   "sha256": hashlib.sha256(raw).hexdigest()},
        "proof_checks": checks, "tools": tool_versions(), "cases": cases,
        "files": {str(path.relative_to(work)): sha256(path) for path in sorted(retained)},
    }
    (work / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def replay(binary, work, cases=None, seed=1):
    if cases and cases.resolve() == binary.resolve():
        raise ValueError("choose a case output distinct from the input ELF")
    address, size = symbol_extent(binary, SYMBOL)
    raw = symbol_bytes(binary, address, size)
    if generate(work) != raw:
        raise ValueError("linked symbol differs from assembled double4.S")
    checks = certify(raw, work)
    corpus = None
    if cases:
        reserved = {work / name for name in ("manifest.json", "symbol.bin", "_CoqProject", "sources", "ExportCases.v")}
        if ((work.resolve() in cases.resolve().parents and cases.exists()) or
                cases.resolve() in {path.resolve() for path in reserved}):
            raise ValueError("case output conflicts with an audit file")
        count = export_cases(raw, work, cases, seed, HERE / "coq/ExportCases.v", "double4")
        retained = work / "conformance.jsonl"
        if cases.resolve() != retained.resolve():
            shutil.copyfile(cases, retained)
        corpus = {"path": retained.name, "count": count, "export_seed": seed}
    write_evidence(binary, address, raw, work, checks, corpus)
    print(f"Coq kernel replay passed for {SYMBOL}, SHA-256 {hashlib.sha256(raw).hexdigest()}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, help="retain the certificate and audit manifest in a new directory")
    parser.add_argument("--cases", type=Path, help="export every modeled vector instruction as conformance JSONL")
    parser.add_argument("--seed", type=int, default=1)
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
        replay(args.elf, args.output, args.cases, args.seed)
    else:
        with tempfile.TemporaryDirectory(prefix="double4-coq-") as temp:
            replay(args.elf, Path(temp), args.cases, args.seed)
