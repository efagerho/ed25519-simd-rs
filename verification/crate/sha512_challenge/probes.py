"""Compare AVX-512 hardware with the Coq rotate, ternary and byte-shuffle steps."""
import ctypes
from pathlib import Path
import random
import subprocess
import tempfile


def vector(values, scope):
    return "[" + ";".join(hex(x) for x in values) + f"]%{scope}"


def check_hardware(workspace, load_path, namespace):
    with tempfile.TemporaryDirectory(prefix="sha512-native-") as tmp:
        work = Path(tmp)
        lib = work / "probe.so"
        subprocess.run(["cc", "-shared", "-nostdlib", Path(__file__).with_name("probes.S"), "-o", lib], check=True)
        hardware = ctypes.CDLL(str(lib))
        round_probe = hardware.sha512_round_probe
        round_probe.argtypes = [ctypes.POINTER(ctypes.c_uint64)]
        round_probe.restype = None
        shuffle_probe = hardware.sha512_shuffle_probe
        shuffle_probe.argtypes = [ctypes.POINTER(ctypes.c_uint8)] * 2
        shuffle_probe.restype = None
        source = [f"From {namespace} Require Import Probe.", "From Coq Require Import List NArith.",
                  "Import ListNotations."]
        rng = random.Random(512)
        for n in range(4):
            words = [rng.getrandbits(64) for _ in range(24)]
            regs = (ctypes.c_uint64 * 32)(*words)
            round_probe(regs)
            source += [f"Example round{n} : flat_map (fun r=>map (observed_round {vector(words, 'N')} r)"
                       f" (seq 0 8)) (seq 0 4) = {vector(regs, 'N')}.",
                       "Proof. vm_compute; reflexivity. Qed."]
            data = rng.sample(range(256), 64)
            mask = list(range(64*n, 64*n+64))
            output = (ctypes.c_uint8 * 64)(*data)
            shuffle_probe(output, (ctypes.c_uint8 * 64)(*mask))
            source += [f"Example shuffle{n} : observed_shuffle {vector(data, 'nat')} {vector(mask, 'nat')}"
                       f" = {vector(output, 'nat')}.", "Proof. vm_compute; reflexivity. Qed."]
        # Retain the observed values alongside the release checks.
        path = Path("Sha512Challenge/Hardware.v")
        (workspace / path).write_text("\n".join(source) + "\n")
        subprocess.run(["coqc", *load_path, path], cwd=workspace, check=True)
