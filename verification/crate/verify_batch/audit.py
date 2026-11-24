"""Check both Rust-facing signature verification theorems against one linked ELF."""
import argparse
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERIFY = HERE.parents[1]
sys.path.insert(0, str(VERIFY))
from crate.post_hash.build import load_callees, symbol_inputs
from elf import symbol_bytes
from evidence import write_evidence
from proof_build import MASK_PROJECTS, compile_libraries, library_flags, write_project

NS = "Ed25519Simd.VerifyBatch"
ENTRIES = {"Zip": "ed25519_simd_zip215_verify_batch", "Dalek": "ed25519_simd_dalek_verify_batch"}
DEPENDENCIES = {
    "prepare_chunk": ("PrepareChunk", "DalekPostHash", "PostHash", "Dalek", "SmallOrder", "KeyTable",
                      "Decode", "Pow2", "FullLadder", "StageRound", "LadderStep", "Double4", "CachedAdd",
                      "Radix16", "Scalar", "SignatureScalar"),
    "zip215": ("Zip215", "Torsion"),
    "sha512_challenge": ("Sha512Challenge", "sha512"),
}
FLAGS = [*library_flags(), "-Q", "VerifyBatch", NS,
         *(arg for group in DEPENDENCIES.values() for ns in group
           for arg in ("-Q", ns, "SHA512" if ns == "sha512" else "Ed25519Simd." + ns))]


def table_inputs(elf, dest):
    # Rust mangles the linkage names. Require one read-only definition of the
    # crate's fully qualified static and check the exact size of its C layout.
    names = subprocess.check_output(["nm", "-S", "-C", "--defined-only", elf], text=True)
    symbols = []
    for label, name, rows, width in (("Identity", "IDENTITY_TABLE", 17, 20),
                                     ("Base", "BASEPOINT_TABLE", 273, 15)):
        symbol = "ed25519_simd::edwards::" + name
        hits = re.findall(rf"^([0-9a-fA-F]+) ([0-9a-fA-F]+) [rR] {re.escape(symbol)}$", names, re.M)
        if len(hits) != 1 or int(hits[0][1], 16) != 8 * rows * width:
            raise ValueError(f"unexpected read-only symbol or layout for {symbol}")
        pc = int(hits[0][0], 16)
        raw = symbol_bytes(elf, pc, 8 * rows * width, readonly_data=True)
        words = struct.iter_unpack("<" + "Q" * width, raw)
        with (dest / (label + "Table.v")).open("w") as f:
            f.write("From Coq Require Import List ZArith.\nImport ListNotations. Open Scope Z_scope.\n")
            f.write(f"Definition address : Z := {pc}.\nDefinition rows : list (list Z) := [\n")
            f.write(";\n".join("[" + ";".join(map(str, row)) + "]" for row in words) + "].\n")
        symbols.append((name, pc, raw))
    return symbols


def check_entries(work):
    statements = []
    lines = [f"Require {NS}.Object."]
    for label, mode in (("Zip", "Zip215"), ("Dalek", "Dalek")):
        theorem = f"{NS}.Object.assembled_{mode.lower()}_verify_batch_correct"
        expected = (f"{NS}.Audit.batch_contract {NS}.Policy.{mode} "
                    f"{NS}.{label}Bytes.address {NS}.{label}Bytes.symbol_bytes")
        lines += [f"Definition checked_{label} : {expected} := {theorem}.", f"Print Assumptions checked_{label}."]
        statements.append(f"{theorem} : {expected}")
    checked = Path("VerifyBatch/Checked.v")
    (work / checked).write_text("\n".join(lines) + "\n")
    assumptions = subprocess.check_output(["coqc", *FLAGS, str(checked)], cwd=work, text=True)
    (work / "assumptions.txt").write_text(assumptions)
    if assumptions.splitlines() != ["Closed under the global context"] * 2:
        raise ValueError(f"unexpected assumptions in batch theorems: {assumptions}")
    # Use Coq's conversion VM for the finite Edwards table check. Both roots
    # and their complete dependencies still go through the standalone checker.
    command = ["coqchk", "-bytecode-compiler", "yes", *FLAGS, "-silent", NS + ".Checked"]
    with (work / "coqchk.log").open("w") as log:
        subprocess.run(command, cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    return {"theorem": "\n".join(statements), "entrypoints": statements, "assumptions": assumptions.strip(),
            "coqchk": {"command": command, "exit_code": 0}}


def replay(elf, work, deps, jobs):
    work.mkdir(parents=True, exist_ok=False)
    compile_libraries(work, projects=MASK_PROJECTS)
    dest = work / "VerifyBatch"
    shutil.copytree(HERE / "coq", dest)
    symbols, _ = symbol_inputs(elf, dest, ENTRIES)
    symbols.extend(table_inputs(elf, dest))
    # A preparation audit contains only ZIP's shared scheduling modules.
    # Load ZIP's complete proof from its own audit of this same executable.
    callees = load_callees(elf, work, deps, DEPENDENCIES, {}, sources_only=True)
    write_project(work, FLAGS, sorted(work.rglob("*.v")))
    subprocess.run(["coq_makefile", "-f", "_CoqProject", "-o", "Makefile"], cwd=work, check=True)
    subprocess.run(["make", "-s", "-j", str(jobs), "VerifyBatch/Object.vo"], cwd=work, check=True)
    checks = check_entries(work)
    src = VERIFY.parent / "src"
    write_evidence(elf, work, "verify_batch", checks, symbols + callees,
                   [src / "wide/avx512ifma/verify_batch.S", src / "verifier/driver.rs", src / "batch.rs"], FLAGS)
    print(f"Checked both production policy entry points in {elf}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--dependencies", type=Path, help="directory of component audits from the same ELF")
    parser.add_argument("--jobs", type=int, default=4, help="maximum parallel proof compilations")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    work = args.output.resolve()
    replay(args.elf.resolve(), work, (args.dependencies or work.with_name(work.name + "-dependencies")).resolve(), args.jobs)
