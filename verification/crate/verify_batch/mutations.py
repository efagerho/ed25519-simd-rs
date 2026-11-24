"""Require the public batch proofs to reject damaged code and an inverted verdict."""
import argparse
import json
from pathlib import Path
import shutil
import tempfile

from audit import ENTRIES, FLAGS, table_inputs
from crate.post_hash.build import symbol_inputs
from crate.post_hash.check_mutations import compile_module, mutate
from elf import load_offset, symbol_bytes, symbol_extent
from evidence import sha256

NS = "VerifyBatch"
RETURN_SLOT = ("spill a table pointer into the caller return slot", "Zip",
               "4c 89 84 24 a8 03 00 00", "4c 89 84 24 e8 03 00 00")
TRANSPOSE = ("interchange keys and message pointers", "Zip", "62 f3 dd 48 43 c6 88", "62 f3 dd 48 43 c6 dd")
CASES = (
    RETURN_SLOT,
    TRANSPOSE,
    ("read past the last tail row", "Dalek", "48 0f 42 f0", "48 0f 46 f0"),
    ("change the output index", "Zip", "48 8b 43 20", "48 8b 43 18"),
    ("shift the stack frame", "Dalek", "48 81 ec c0 03 00 00", "48 81 ec d0 03 00 00"),
    ("hash the key twice", "Dalek", "49 8d b7 00 01 00 00", "49 8d b7 00 00 00 00"),
)


def redirected(elf):
    name = ENTRIES["Zip"]
    pc, size = symbol_extent(elf, name)
    code = symbol_bytes(elf, pc, size)
    # The direct call after the final prepare argument must resolve to the
    # permissive preparation entry. Point it at the strict entry in this ELF.
    prefix = bytes.fromhex("48 8d 8c 24 00 03 00 00 e8")
    if code.count(prefix) != 1:
        raise ValueError("ambiguous preparation call site")
    pos = code.index(prefix) + len(prefix)
    next_pc = pc + pos + 4
    old = code[pos:pos+4]
    if next_pc + int.from_bytes(old, "little", signed=True) != symbol_extent(elf, "ed25519_simd_prepare_chunk")[0]:
        raise ValueError("unexpected original preparation target")
    new = (symbol_extent(elf, "ed25519_simd_dalek_prepare_chunk")[0] - next_pc).to_bytes(4, "little", signed=True)
    return "call Dalek preparation in ZIP-215", "Zip", (prefix + old).hex(), (prefix + new).hex()


def check(elf, audit, work):
    manifest = json.loads((audit / "manifest.json").read_text())
    if sha256(elf) != manifest["elf"]["sha256"]:
        raise ValueError("audit belongs to a different ELF")
    for path in audit.iterdir():
        if path.is_dir() and path.name not in (NS, "sources"):
            (work / path.name).symlink_to(path)
    dest = work / NS
    shutil.copytree(audit / NS, dest)
    for module in ("RejectedBatch", "DecoderY"):
        shutil.copyfile(Path(__file__).with_name("tests") / f"{module}.v", dest / f"{module}.v")
        compile_module(work, FLAGS, NS, module)
    print("Both policy entries returned a confined rejection on the padded single-row control", flush=True)
    print("The decoder preserved the sign mask and noncanonical Y in all eight scratch lanes", flush=True)
    for description, label, old, new in (*CASES, redirected(elf)):
        damaged = work / "mutated.elf"
        mutate(elf, damaged, ENTRIES[label], old, new)
        _, modules = symbol_inputs(damaged, dest, ENTRIES)
        for module in modules:
            compile_module(work, FLAGS, NS, module)
        compile_module(work, FLAGS, NS, "Object", reject=True)
        control = {RETURN_SLOT[0]: "ReturnSlot", TRANSPOSE[0]: "Transpose"}.get(description)
        if control:
            filename = control + ".v"
            shutil.copyfile(Path(__file__).with_name("tests") / filename, dest / filename)
            compile_module(work, FLAGS, NS, control)
        print(f"Batch theorem rejected mutation: {description}", flush=True)

    # Restore the linked bytes and reverse the public mathematical verdict.
    # This checks that a successful byte comparison alone cannot pass the audit.
    _, modules = symbol_inputs(elf, dest, ENTRIES)
    for module in modules:
        compile_module(work, FLAGS, NS, module)
    contract = dest / "Audit.v"
    source = contract.read_text()
    exact = "v=true <-> signature_accepts"
    if source.count(exact) != 1:
        raise ValueError("missing verdict specification")
    contract.write_text(source.replace(exact, "v=false <-> signature_accepts"))
    compile_module(work, FLAGS, NS, "Audit")
    compile_module(work, FLAGS, NS, "Object", reject=True, diagnostic="while it is expected to have type")
    print("Batch theorem rejected an inverted acceptance specification", flush=True)

    # Damage the linked identity table and show that the public contract is
    # now logically false, for either policy and any entry point.
    damaged = work / "mutated.elf"
    shutil.copyfile(elf, damaged)
    identity = next(s for s in manifest["symbols"] if s["name"] == "IDENTITY_TABLE")
    with damaged.open("r+b") as f:
        f.seek(load_offset(f, identity["address"], identity["size"], readonly_data=True))
        if f.read(1) != b"\x01":
            raise ValueError("unexpected first limb in the valid identity table")
        f.seek(-1, 1)
        f.write(b"\x00")
    table_inputs(damaged, dest)
    shutil.copyfile(audit / NS / "Audit.v", contract)
    for module in ("IdentityTable", "LoadedImage", "RejectCall", "ScalarInputs", "BatchScalar", "BatchDecode", "DecoderSave", "DecoderProduct", "KeySquare", "SetupTail", "NativeScale", "PairedSetup", "DecoderPower", "NativeWords", "SetupValues", "PowerInputs", "PowerWrites", "DecoderResume", "DecoderFinish", "FinishSquare", "FinishProduct", "RootTest", "RootMasks", "RootAccept", "RootDecision", "Selection", "PrepareUnwind", "RejectDispatch", "RejectFinish", "RejectExecution", "Tables", "Audit"):
        compile_module(work, FLAGS, NS, module)
    (dest / "DamagedTable.v").write_text(
        "From Ed25519Simd.VerifyBatch Require Import Audit Tables.\n"
        "Goal forall mode pc text, ~ batch_contract mode pc text.\n"
        "Proof. intros mode pc text H. "
        "destruct (static_tables _ _ _ H) as [_ [_ Check]]. vm_compute in Check; discriminate. Qed.\n")
    compile_module(work, FLAGS, NS, "DamagedTable")
    print("A corrupted linked identity-table limb falsified both public contracts", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        check(args.elf.resolve(), args.audit.resolve(), Path(temp))
