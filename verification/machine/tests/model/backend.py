"""Evaluate batches with the installed Coq VM; keep compiler output out of the source tree."""
from pathlib import Path
import re
import subprocess
import sys

from case_data import OPS

sys.path.append(str(Path(__file__).resolve().parents[3]))
from proof_build import compile_libraries


def words(values):
    return "[" + ";".join(hex(n) for n in values) + "]"


def expression(case):
    mnemonic, dst, *src = case["instruction"]
    op, kinds = OPS[mnemonic]
    args = " ".join(f"({n})" if n < 0 else str(n) for n in src)
    overrides = ";".join(f"({r}%nat,{words(v)})" for r, v in case.get("registers", {}).items())
    base, disp = src[-2:] if kinds.endswith("bd") else (0, 0)
    return (f"Eval vm_compute in prediction ({dst}%nat, {op} {args}) [{overrides}] "
            f"{base}%nat ({disp}) {words(case.get('memory', []))}.")


class Model:
    def __init__(self, root, work):
        compile_libraries(work, projects=(root.name,), source=root.parent)
        self.work = work / root.name
        self.flags = ["-Q", ".", "Machine"]

    def predict(self, cases):
        header = ("From Coq Require Import ZArith List Strings.String.\n"
                  "From Machine Require Import isa.Instructions tests.model.Oracle.\n"
                  "Import ListNotations. Open Scope Z_scope. Set Printing Width 10000.\n")
        # Bound Coq's live syntax tree even for long hardware campaigns.
        for i in range(0, len(cases), 32):
            batch = cases[i:i+32]
            (self.work / "Batch.v").write_text(header + "\n".join(map(expression, batch)))
            output = subprocess.check_output(["coqc", *self.flags, "Batch.v"], cwd=self.work, text=True)
            rows = re.findall(r'= "(invalid|[-0-9 |]+)"', output)
            if len(rows) != len(batch):
                raise ValueError(f"unexpected Coq output for batch beginning with {batch[0]['id']}")
            for row in rows:
                if row == "invalid":
                    yield None, None
                    continue
                encoded, result = row.split("|")
                lanes = list(map(int, result.split()))
                if len(lanes) != 8:
                    raise ValueError("incomplete Coq destination")
                yield bytes(map(int, encoded.split())), lanes

    def block_probe(self, name, inputs=None):
        """Evaluate the complete block program and serialize the observed machine state."""
        module, report, defaults, columns = {
            "packed": ("PackedRows", "packed_report", "seeds", 49),
            "indexed": ("Indexed", "indexed_report", "seeds", 33),
            "mask": ("Mask", "mask_report", "seeds", 2),
            "filter": ("Filter", "filter_report", "seeds", 2),
            "control": ("Control", "probe_report", "counts", 4),
            "mixed": ("Mixed", "mixed_report", "seeds", 3 + 32*8 + 3*8),
            "prologue": ("Prologue", "prologue_report", "seeds", 4 + 32*8 + 31*8 + 3*4*8),
            "aligned": ("Aligned", "aligned_report", "seeds", 8 + 32*8 + 20*8 + 8),
        }[name]
        values = defaults
        if inputs is not None:
            if not isinstance(inputs, list) or not inputs or not all(
                    type(n) is int and 0 <= n < 2**64 for n in inputs):
                raise ValueError(f"invalid {name} probe inputs")
            values = words(inputs)
        source = self.work / "ProbeResults.v"
        source.write_text(f"From Machine Require Import tests.{module}.\n"
                          "From Coq Require Import List ZArith Strings.String.\n"
                          "Import ListNotations. Open Scope Z_scope. Set Printing Width 100000.\n"
                          f"Eval vm_compute in {report} {values}.\n")
        output = subprocess.check_output(["coqc", *self.flags, source.name], cwd=self.work, text=True)
        match = re.search(r'= "([0-9 |]+)"', output)
        if not match:
            raise ValueError(f"unexpected Coq output for the {name} probe")
        encoded, *cases = match[1].split("|")
        rows = [list(map(int, case.split())) for case in cases]
        if not rows or any(len(row) != columns for row in rows):
            raise ValueError(f"{name} probe did not return the complete observation with a restored stack")
        return bytes(map(int, encoded.split())), rows
