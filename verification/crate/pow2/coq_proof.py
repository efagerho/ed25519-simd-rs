"""Generate the Coq program, check it against the linked ELF and replay its theorem."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import random
import shutil
import subprocess
import tempfile

from certify import certify
from proof_build import COMPONENTS, component_flags
from evidence import write_evidence
from disassembly import SYMBOL
from elf import require, symbol_bytes, symbol_extent
from generate_listing import generate


def export_cases(raw, work, dest, seed, source=None, tag="pow2"):
    source = source or Path(__file__).parent / "coq/ExportCases.v"
    destination = work / COMPONENTS[tag] / source.name
    destination.parent.mkdir(exist_ok=True)
    shutil.copyfile(source, destination)
    output = subprocess.check_output(["coqc", *component_flags(tag), str(destination.relative_to(work))], cwd=work, text=True)
    match = re.search(r'= "([^"]+)"', output)
    require(match, "Coq did not export the kernel rows")
    symbol_hash = hashlib.sha256(raw).hexdigest()
    rng = random.Random(seed)
    rows = []
    counts, *kernel_rows = match[1].split("|")
    coverage_tag, caller_sites, caller_forms = counts.split()
    require(coverage_tag == "caller", "missing Coq caller coverage counts")
    for row in kernel_rows:
        offset, length, mnemonic, *args = row.split()
        off, size = int(offset), int(length)
        operands = list(map(int, args))
        require(0 <= off < off + size <= len(raw), "kernel row outside linked symbol")
        # Preserve every architectural input, independently of operand aliasing.
        rows.append({"id": f"{tag}/+0x{off:04x}", "instruction": [mnemonic, *operands],
                     "registers": {str(reg): [rng.getrandbits(64) for _ in range(8)]
                                   for reg in range(32)},
                     "memory": [rng.getrandbits(64) for _ in range(8)],
                     "bytes": raw[off:off+size].hex(), "symbol_sha256": symbol_hash,
                     "export_seed": seed})
    dest.write_text("".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows))
    print(f"{caller_sites} scalar/control sites use {caller_forms} forms covered by the native probes.")
    print(f"Exported {len(rows)} linked kernel rows to {dest}")
    return len(rows)


def replay(binary, work, cases=None, seed=1):
    if cases and cases.resolve() == binary.resolve():
        raise ValueError("choose a case output distinct from the input ELF")
    address, size = symbol_extent(binary, SYMBOL)
    raw = symbol_bytes(binary, address, size)
    assembled = generate(work)
    if raw != assembled:
        offset = next((i for i, (a, b) in enumerate(zip(raw, assembled)) if a != b),
                      min(len(raw), len(assembled)))
        raise ValueError(f"linked symbol differs from assembled pow2.S at +0x{offset:x}")
    checks = certify(raw, work)
    corpus = None
    if cases:
        reserved = {work / name for name in ("manifest.json", "symbol.bin", "_CoqProject", "sources", "Pow2/ExportCases.v")}
        if ((work.resolve() in cases.resolve().parents and cases.exists()) or
                cases.resolve() in {path.resolve() for path in reserved}):
            raise ValueError("case output conflicts with an audit file")
        count = export_cases(raw, work, cases, seed)
        retained = work / "conformance.jsonl"
        if cases.resolve() != retained.resolve():
            shutil.copyfile(cases, retained)
        corpus = {"path": retained.name, "count": count, "export_seed": seed}
    source = Path(__file__).resolve().parents[3] / "src/wide/avx512ifma/pow2.S"
    write_evidence(binary, work, "pow2", checks, [(SYMBOL, address, raw)], [source],
                   component_flags("pow2"), corpus)
    print(f"Coq kernel replay passed for ed25519_simd_pow2_ifma, SHA-256 {hashlib.sha256(raw).hexdigest()}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, help="retain proof sources, check logs, corpus and audit manifest in a new directory")
    parser.add_argument("--cases", type=Path, help="export the verified kernel rows as conformance JSONL")
    parser.add_argument("--seed", type=int, default=1, help="seed for exported register and memory inputs")
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=False)
        replay(args.elf, args.output, args.cases, args.seed)
    else:
        with tempfile.TemporaryDirectory(prefix="pow2-coq-") as tmp:
            replay(args.elf, Path(tmp), args.cases, args.seed)
