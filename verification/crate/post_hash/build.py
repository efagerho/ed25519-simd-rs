"""Replay post-hash callees and share the ABI and scalar-product proofs."""
from pathlib import Path
import json
import shutil
import subprocess
import sys

from elf import symbol_bytes, symbol_extent
from evidence import sha256
from proof_build import COMPONENTS, write_symbol_bytes

HERE = Path(__file__).resolve().parent
SHARED_FLAGS = ["-Q", "PostHash", "Ed25519Simd.PostHash"]


def symbol_inputs(elf, dest, entries):
    symbols = []
    modules = []
    for label, name in entries.items():
        address, size = symbol_extent(elf, name)
        raw = symbol_bytes(elf, address, size)
        module = label + "Bytes"
        path = dest / (module + ".v")
        write_symbol_bytes(path, raw)
        with path.open("a") as f:
            f.write(f"Definition address : Z := {address}.\n")
        symbols.append((name, address, raw))
        modules.append(module)
    return symbols, modules


def load_callees(elf, work, dependencies, components_to_load, overrides, *, sources_only=False):
    dep_symbols = {}
    digest = sha256(elf)
    components = {ns: component for component, ns in COMPONENTS.items()}
    proof_roots = {ns: HERE.parent / name / "coq" for ns, name in components.items()}
    proof_roots.update(PostHash=HERE, sha512=HERE.parents[1] / "sha512")
    for name, namespaces in components_to_load.items():
        parent = overrides.get(name, dependencies)
        audit = parent / (name.replace("_", "-") + "-audit")
        if not audit.exists():
            subprocess.run([sys.executable, "-B", str(HERE.parent / name / "audit.py"),
                            str(elf), "--output", str(audit)], check=True)
        manifest = json.loads((audit / "manifest.json").read_text())
        if manifest["elf"]["sha256"] != digest:
            raise ValueError(f"{audit} was built against a different ELF")
        for symbol in manifest["symbols"]:
            entry = symbol["name"]
            if entry in ("scalar_order", "sha512_literals"):
                # The callee certificate checks all RIP-relative operands and literal bytes.
                pc = symbol["address"]
                raw = symbol_bytes(elf, pc, 32 if entry == "scalar_order" else 832, readonly_data=True)
            else:
                pc, size = symbol_extent(elf, entry)
                raw = symbol_bytes(elf, pc, size)
            if (pc != symbol["address"] or raw != (audit / symbol["path"]).read_bytes()):
                raise ValueError(f"callee evidence differs from ELF for {entry}")
            dep_symbols[entry] = (entry, pc, raw)
        for ns in namespaces:
            if sources_only:
                (work / ns).mkdir()
            for source in (audit / ns).glob("*.v"):
                checked_in = proof_roots[ns] / source.name
                if sha256(source) != manifest["files"][f"{ns}/{source.name}"]:
                    raise ValueError(f"corrupt callee proof source {source}")
                if checked_in.exists() and source.read_bytes() != checked_in.read_bytes():
                    raise ValueError(f"callee evidence predates the current {checked_in}")
                if sources_only and source.name != "Checked.v":
                    shutil.copyfile(source, work / ns / source.name)
            if not sources_only:
                shutil.copytree(audit / ns, work / ns, ignore=shutil.ignore_patterns("Checked.*"))
    return list(dep_symbols.values())


def compile_shared(work, flags):
    (work / "PostHash").mkdir()
    for name in ("Staging", "Product", "Lanes"):
        source = Path("PostHash") / (name + ".v")
        shutil.copyfile(HERE / source.name, work / source)
        subprocess.run(["coqc", *flags, str(source)], cwd=work, check=True)
    # The decoder certificate supplies an extra pow2 address in DecoderBytes.
    subprocess.run(["coqc", *flags, "Dalek/Object.v"], cwd=work, check=True)
