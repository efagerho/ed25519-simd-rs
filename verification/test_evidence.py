"""Regression tests for portable verification evidence; no Coq or hardware required."""
import argparse
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / "machine/tests"), str(HERE / "pow2"), str(HERE / "double4")]
import audit as double4_audit
import case_data
import coq_proof
import evidence
import run


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)
        self.case = {"id": "linked/load", "instruction": ["vmovdqu64", 31, 8, 64],
                     "registers": {"31": [2**64-1] * 8}, "memory": [2**63+i for i in range(8)],
                     "expected": [2**63+i for i in range(8)], "bytes": "62", "export_seed": 42,
                     "symbol_sha256": "0123456789abcdef" * 4}

    def args(self, **overrides):
        values = dict(backend="model", cases=[], case=None, replay=None, probe=None, record={},
                      random=0, seed=1, xed_kit=None, report=self.work / "report.json",
                      failure=self.work / "failure.json")
        return argparse.Namespace(**{**values, **overrides})

    def execute(self, args):
        # These tests exercise the real input/report/replay path; only the
        # external model and version query are replaced with deterministic data.
        with patch.object(run, "Model") as model, patch.object(run.subprocess, "check_output", return_value="Coq test\n"), \
                contextlib.redirect_stdout(io.StringIO()):
            model.return_value.predict.side_effect = lambda cases: [
                (bytes.fromhex(case["bytes"]), case["memory"]) for case in cases]
            run.run(args, self.work)
        return json.loads(args.report.read_text())

    def test_export_seed_42_and_all_inputs_survive_report_replay(self):
        corpus = self.work / "input.jsonl"
        corpus.write_text(json.dumps(self.case) + "\n")
        first = self.execute(self.args(cases=[corpus]))
        corpus.unlink()  # A report must stand on its own.
        self.assertEqual(first["export_seeds"], [42])
        self.assertEqual(first["campaign_seeds"], [])
        self.assertNotIn("seed", first)
        row = first["checked"][0]
        self.assertEqual(set(row["registers"]), case_data.REGISTER_IDS)
        self.assertEqual(row["registers"]["31"], [2**64-1] * 8)
        self.assertEqual(row["registers"]["30"], list(range(240, 248)))
        for key in ("memory", "expected", "symbol_sha256", "export_seed"):
            self.assertEqual(row[key], self.case[key])
        second = self.execute(self.args(replay=self.work / "report.json", record=first, seed=999,
                                         report=self.work / "replayed.json"))
        self.assertEqual(first["checked"], second["checked"])
        self.assertEqual(first["corpus_sha256"], second["corpus_sha256"])
        self.assertEqual(second["export_seeds"], [42])

    def test_campaign_and_export_provenance_remain_distinct(self):
        generated = list(case_data.campaign(19, 1))[0]
        self.assertEqual(generated["campaign_seed"], 19)
        generated.update(instruction=self.case["instruction"], memory=self.case["memory"], bytes="62")
        corpus = self.work / "mixed.jsonl"
        corpus.write_text("\n".join(map(json.dumps, [self.case, generated])))
        report = self.execute(self.args(cases=[corpus], seed=1))
        self.assertEqual(report["campaign_seeds"], [19])
        self.assertEqual(report["export_seeds"], [42])

    def test_report_rejects_missing_inputs_and_changed_corpus(self):
        row = run.complete_case(self.case, b"\x62")
        report = {"schema_version": 2, "checked": [row], "corpus_sha256": run.corpus_digest([row])}
        changed = copy.deepcopy(report)
        changed["checked"][0]["memory"][0] += 1
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            run.replay_cases(changed)
        del report["checked"][0]["registers"]["0"]
        with self.assertRaisesRegex(ValueError, "incomplete"):
            run.replay_cases(report)
        with self.assertRaisesRegex(ValueError, "replayable"):
            run.replay_cases({"checked": [self.case]})

    def test_legacy_failure_inputs_are_still_replayable(self):
        self.assertEqual(run.replay_cases({"case": self.case, "seed": 1}), [self.case])

    def test_success_report_replays_recorded_native_probes(self):
        row = run.complete_case(self.case, b"\x62")
        record = {"schema_version": 2, "checked": [row], "corpus_sha256": run.corpus_digest([row]),
                  "control_probe": {"input_rcx": [1], "bytes": "c3"},
                  "mixed_probe": {"seeds": [9], "bytes": "c3"},
                  "aligned_probe": {"seeds": [0, 1, 2, 3, 2**64-1], "bytes": "55"}}
        with patch("native.backend.require_host"), patch("native.backend.Native") as native, \
                patch.object(run, "cpu_info", return_value={"processor": "0"}), \
                patch.object(run, "check_probe") as probe:
            wanted = case_data.registers(row)
            wanted[31] = row["memory"]
            native.return_value.execute.return_value = {"registers": wanted}
            self.execute(self.args(backend="native", replay=self.work / "old.json", record=record))
            self.assertEqual([call.args[0] for call in probe.call_args_list], ["control", "mixed", "aligned"])


class ReleaseEvidenceTests(unittest.TestCase):
    def test_double4_rejects_changed_linked_bytes_before_certification(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            with patch.object(double4_audit, "symbol_extent", return_value=(4096, 2)), \
                    patch.object(double4_audit, "symbol_bytes", return_value=b"\x55\xc3"), \
                    patch.object(double4_audit, "generate", return_value=b"\x5d\xc3"), \
                    patch.object(double4_audit, "certify") as certify:
                with self.assertRaisesRegex(ValueError, "linked symbol differs"):
                    double4_audit.replay(work / "release.elf", work)
                certify.assert_not_called()

    def test_double4_export_uses_its_own_program_and_case_ids(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            source = HERE / "double4/coq/ExportCases.v"
            with patch.object(coq_proof.subprocess, "check_output", return_value='= "caller 1 1|0 1 vpsubq 0 1 0"\n'), \
                    contextlib.redirect_stdout(io.StringIO()):
                coq_proof.export_cases(b"\x62", work, work / "cases.jsonl", 42, source, "double4")
            row = json.loads((work / "cases.jsonl").read_text())
            self.assertEqual(row["id"], "double4/+0x0000")
            self.assertEqual(row["instruction"], ["vpsubq", 0, 1, 0])
            self.assertEqual((work / "ExportCases.v").read_bytes(), source.read_bytes())
            case_data.validate(row)

    def test_export_preserves_seed_and_full_register_state(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            output = '= "caller 1 1|0 1 vpmadd52luq 0 0 0"\n'
            with patch.object(coq_proof.subprocess, "check_output", return_value=output), \
                    contextlib.redirect_stdout(io.StringIO()):
                coq_proof.export_cases(b"\x62", work, work / "cases.jsonl", 42)
            row = json.loads((work / "cases.jsonl").read_text())
            self.assertEqual(row["export_seed"], 42)
            self.assertEqual(set(row["registers"]), case_data.REGISTER_IDS)
            self.assertEqual(row["symbol_sha256"], hashlib.sha256(b"\x62").hexdigest())
            case_data.validate(row)

    def test_manifest_binds_proof_sources_checks_bytes_and_corpus(self):
        for module, routine, generator in ((evidence, "pow2", "sources/coq_proof.py"),
                                            (double4_audit, "double4", "sources/double4/audit.py")):
            with self.subTest(routine=routine):
                self.check_manifest(module, routine, generator)

    def check_manifest(self, module, routine, generator):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            (work / "machine").mkdir()
            artifacts = {"Program.v": "Definition program := 0.\n", "Audit.v": "Definition contract := True.\n",
                         "FieldSpec.v": "Definition exponent := 1.\n", "machine/X86.v": "Definition bits := 64.\n",
                         "machine/_CoqProject": "-Q . Machine\nX86.v\n", f"{routine}.expanded.S": "ret\n",
                         "assumptions.txt": "Closed under the global context\n", "coqchk.log": "",
                         "conformance.jsonl": '{"export_seed":42}\n', "release.elf": "example ELF"}
            for name, value in artifacts.items():
                (work / name).write_text(value)
            checks = {"assumptions": "Closed under the global context",
                      "coqchk": {"command": ["coqchk", "-silent", "Object"], "exit_code": 0}}
            corpus = {"path": "conformance.jsonl", "count": 1, "export_seed": 42}
            with patch.object(module, "tool_versions", return_value={"coqc": {"version": "test"}}):
                module.write_evidence(work / "release.elf", 4096, b"\xc3", work, checks, corpus)
            manifest = json.loads((work / "manifest.json").read_text())
            self.assertEqual(manifest["proof_checks"], checks)
            self.assertEqual(manifest["cases"], corpus)
            self.assertEqual(manifest["symbol"]["sha256"], hashlib.sha256(b"\xc3").hexdigest())
            self.assertEqual(manifest["elf"]["sha256"], evidence.sha256(work / "release.elf"))
            for name, digest in manifest["files"].items():
                self.assertEqual(evidence.sha256(work / name), digest)
            self.assertIn("FieldSpec.v", manifest["files"])
            self.assertIn("machine/X86.v", manifest["files"])
            self.assertIn(generator, manifest["files"])
            self.assertIn("Program.v\n", (work / "_CoqProject").read_text())
            (work / "FieldSpec.v").write_text("Definition exponent := 2.\n")
            self.assertNotEqual(evidence.sha256(work / "FieldSpec.v"), manifest["files"]["FieldSpec.v"])


if __name__ == "__main__":
    unittest.main()
