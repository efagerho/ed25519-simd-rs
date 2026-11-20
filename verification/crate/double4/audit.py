"""Replay the complete double4 certificate against a linked ELF symbol."""
import argparse
import hashlib
from pathlib import Path
import shutil
import tempfile

from certificate import certify
from listing import SYMBOL, SOURCE, generate
from coq_proof import export_cases
from elf import symbol_bytes, symbol_extent
from evidence import write_evidence

from proof_build import component_flags

HERE = Path(__file__).resolve().parent


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
        reserved = {work / name for name in ("manifest.json", "symbol.bin", "_CoqProject", "sources", "Double4/ExportCases.v")}
        if ((work.resolve() in cases.resolve().parents and cases.exists()) or
                cases.resolve() in {path.resolve() for path in reserved}):
            raise ValueError("case output conflicts with an audit file")
        count = export_cases(raw, work, cases, seed, HERE / "coq/ExportCases.v", "double4")
        retained = work / "conformance.jsonl"
        if cases.resolve() != retained.resolve():
            shutil.copyfile(cases, retained)
        corpus = {"path": retained.name, "count": count, "export_seed": seed}
    write_evidence(binary, work, "double4", checks, [(SYMBOL, address, raw)], [SOURCE],
                   component_flags("double4"), corpus)
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
