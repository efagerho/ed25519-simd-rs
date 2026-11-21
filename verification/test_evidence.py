"""Regression tests for portable verification evidence; no Coq or hardware required."""
import argparse
import contextlib
import copy
import hashlib
import io
import importlib.util
import json
import os
from pathlib import Path
import sys
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / "machine/tests"), str(HERE / "crate/pow2"), str(HERE / "crate/double4")]
import audit as double4_audit
import case_data
import coq_proof
import evidence
import elf
import proof_build
import run


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


with patch.dict(sys.modules, {
        "certificate": load_module("cached_add_certificate", HERE / "crate/cached_add/certificate.py"),
        "listing": load_module("cached_add_listing", HERE / "crate/cached_add/listing.py")}):
    cached_add_audit = load_module("cached_add_audit", HERE / "crate/cached_add/audit.py")

with patch.dict(sys.modules, {
        "certificate": load_module("scalar_certificate", HERE / "crate/scalar/certificate.py"),
        "listing": load_module("scalar_listing", HERE / "crate/scalar/listing.py")}):
    scalar_audit = load_module("scalar_audit", HERE / "crate/scalar/audit.py")


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
    def test_proofs_reject_changed_linked_bytes_before_certification(self):
        for module in (double4_audit, cached_add_audit, scalar_audit):
            with self.subTest(module=module.__name__), tempfile.TemporaryDirectory() as tmp:
                work = Path(tmp)
                with patch.object(module, "symbol_extent", return_value=(4096, 2)), \
                        patch.object(module, "symbol_bytes", return_value=b"\x55\xc3"), \
                        patch.object(module, "generate", return_value=b"\x5d\xc3"), \
                        patch.object(module, "certify") as certify:
                    with self.assertRaisesRegex(ValueError, "linked symbol differs"):
                        module.replay(work / "release.elf", work)
                    certify.assert_not_called()

    def test_cached_add_exports_memory_source_ifma(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            source = HERE / "crate/cached_add/coq/ExportCases.v"
            with patch.object(coq_proof.subprocess, "check_output", return_value='= "caller 1 1|0 1 vpmadd52huq_mem 31 16 8 320"\n'), \
                    contextlib.redirect_stdout(io.StringIO()):
                coq_proof.export_cases(b"\x62", work, work / "cases.jsonl", 42, source, "cached_add")
            row = json.loads((work / "cases.jsonl").read_text())
            self.assertEqual(row["id"], "cached_add/+0x0000")
            self.assertEqual(row["instruction"], ["vpmadd52huq_mem", 31, 16, 8, 320])
            self.assertEqual((work / "CachedAdd/ExportCases.v").read_bytes(), source.read_bytes())
            case_data.validate(row)

    def test_double4_export_uses_its_own_program_and_case_ids(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            source = HERE / "crate/double4/coq/ExportCases.v"
            with patch.object(coq_proof.subprocess, "check_output", return_value='= "caller 1 1|0 1 vpsubq 0 1 0"\n'), \
                    contextlib.redirect_stdout(io.StringIO()):
                coq_proof.export_cases(b"\x62", work, work / "cases.jsonl", 42, source, "double4")
            row = json.loads((work / "cases.jsonl").read_text())
            self.assertEqual(row["id"], "double4/+0x0000")
            self.assertEqual(row["instruction"], ["vpsubq", 0, 1, 0])
            self.assertEqual((work / "Double4/ExportCases.v").read_bytes(), source.read_bytes())
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
        for module, routine, namespace, generator in ((evidence, "pow2", "Pow2", "sources/coq_proof.py"),
                                            (double4_audit, "double4", "Double4", "sources/double4/audit.py"),
                                            (cached_add_audit, "add_cached", "CachedAdd", "sources/cached_add/audit.py"),
                                            (scalar_audit, "reduce", "Scalar", "sources/scalar/audit.py"),
                                            (evidence, "ladder_step", "LadderStep", "sources/ladder_step/audit.py"),
                                            (evidence, "digest_to_radix16", "Radix16", "sources/radix16/audit.py"),
                                            (evidence, "dalek_recompress", "Dalek", "sources/dalek_recompress/audit.py")):
            with self.subTest(routine=routine):
                self.check_manifest(module, routine, namespace, generator)

    def check_manifest(self, module, routine, namespace, generator):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            artifacts = {f"{namespace}/Program.v": "Definition program := 0.\n",
                         f"{namespace}/Audit.v": "Definition contract := True.\n",
                         "curve25519/Field.v": "Definition prime := 31.\n",
                         "crate/Wide51.v": "Definition lanes := 8.\n", "machine/isa/X86.v": "Definition bits := 64.\n",
                         "machine/_CoqProject": "-Q . Machine\nisa/X86.v\n",
                         "arithmetic/_CoqProject": "-Q . ProofArithmetic\nExpressions.v\n",
                         "arithmetic/Expressions.v": "Definition atom := 0.\n", f"{routine}.expanded.S": "ret\n",
                         "assumptions.txt": "Closed under the global context\n", "coqchk.log": "",
                         "conformance.jsonl": '{"export_seed":42}\n', "release.elf": "example ELF"}
            for name, value in artifacts.items():
                (work / name).parent.mkdir(parents=True, exist_ok=True)
                (work / name).write_text(value)
            checks = {"assumptions": "Closed under the global context",
                      "coqchk": {"command": ["coqchk", "-silent", f"Ed25519Simd.{namespace}.Checked"], "exit_code": 0}}
            corpus = {"path": "conformance.jsonl", "count": 1, "export_seed": 42}
            component = next(k for k, v in proof_build.COMPONENTS.items() if v == namespace)
            theorem, contract = proof_build.public_statement(component)
            checks["theorem"] = f"{theorem} : {contract}"
            symbols = [(routine, 4096, b"\xc3")]
            if component == "ladder_step":
                symbols.extend([("double4", 8192, b"a"), ("add_cached", 12288, b"b")])
            elif component == "dalek_recompress":
                symbols.extend([("decoder", 8192, b"d"), ("helper", 12288, b"h"), ("small", 16384, b"s")])
            elif component == "radix16":
                symbols.append(("scalar_reduce", 8192, b"a"))
            with patch.object(evidence, "tool_versions", return_value={"coqc": {"version": "test"}}):
                evidence.write_evidence(work / "release.elf", work, component, checks, symbols, [],
                                        proof_build.component_flags(component), corpus)
            manifest = json.loads((work / "manifest.json").read_text())
            self.assertEqual(manifest["proof_checks"], checks)
            self.assertEqual([s["address"] for s in manifest["symbols"]], [s[1] for s in symbols])
            self.assertEqual(manifest["cases"], corpus)
            self.assertEqual(manifest["symbol"]["sha256"], hashlib.sha256(b"\xc3").hexdigest())
            self.assertEqual(manifest["elf"]["sha256"], evidence.sha256(work / "release.elf"))
            for name, digest in manifest["files"].items():
                self.assertEqual(evidence.sha256(work / name), digest)
            self.assertIn("curve25519/Field.v", manifest["files"])
            self.assertIn("crate/Wide51.v", manifest["files"])
            self.assertIn("-Q crate Ed25519Simd\n", (work / "_CoqProject").read_text())
            self.assertIn("machine/isa/X86.v", manifest["files"])
            self.assertIn("arithmetic/Expressions.v", manifest["files"])
            self.assertIn("arithmetic/_CoqProject", manifest["files"])
            self.assertIn("sources/proof_build.py", manifest["files"])
            self.assertIn("-Q arithmetic ProofArithmetic\n", (work / "_CoqProject").read_text())
            self.assertIn(generator, manifest["files"])
            if component == "radix16":
                self.assertIn("sources/scalar/listing.py", manifest["files"])
                self.assertEqual((work / "scalar_reduce.bin").read_bytes(), b"a")
            if component == "dalek_recompress":
                for dependency in ("decompress_r", "small_order"):
                    self.assertIn(f"sources/{dependency}/audit.py", manifest["files"])
                self.assertIn("sources/mask_listing.py", manifest["files"])
            project = (work / "_CoqProject").read_text().splitlines()
            self.assertIn(f"-Q {namespace} Ed25519Simd.{namespace}", project)
            self.assertIn(f"{namespace}/Program.v", project)
            self.assertIn(f"{namespace}/Audit.v", manifest["files"])
            self.assertTrue(manifest["theorem"].startswith(f"Ed25519Simd.{namespace}.Object."))
            (work / "curve25519/Field.v").write_text("Definition prime := 17.\n")
            self.assertNotEqual(evidence.sha256(work / "curve25519/Field.v"), manifest["files"]["curve25519/Field.v"])


class LinkedElfTests(unittest.TestCase):
    def test_release_mapping(self):
        # One text section with an independently supplied program-header mapping.
        ident = b"\x7fELF\x02\x01" + bytes(10)
        data = b"abcd"
        segment = (1, 5, 256, 4096, 0, 4, 4, 1)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "fixture"
            def check(segments, section_offset=256, kind=3):
                header = elf.ELF_HEADER.pack(ident, kind, 62, 1, 0, 64, 0, 0, 64,
                                             56, len(segments), 0, 0, 0)
                headers = b"".join(elf.PROGRAM_HEADER.pack(*s) for s in segments)
                path.write_bytes((header+headers).ljust(256, b"\0") + data)
                section = f"  0 .text 00000004 00001000 00001000 {section_offset:x}"
                with patch.object(elf.subprocess, "check_output", return_value=section):
                    return elf.symbol_bytes(path, 4097, 3)
            self.assertEqual(check([segment]), b"bcd")
            self.assertEqual(check([segment], kind=2), b"bcd")
            for args in [([segment], 255), ([segment, segment],),
                         ([(1, 4, 256, 4096, 0, 4, 4, 1)],),
                         ([(1, 5, 256, 4096, 0, 3, 4, 1)],),
                         ([(1, 5, 256, 4096, 0, 5, 5, 1)],), ([segment], 256, 1)]:
                with self.subTest(args=args), self.assertRaises(ValueError):
                    check(*args)


class SharedLibraryTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("coqc"), "requires Coq")
    def test_closed_but_weakened_theorem_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            component = work / "Double4"
            component.mkdir()
            flags = ["-Q", "Double4", "Ed25519Simd.Double4"]
            modules = {"ObjectBytes": "Definition symbol_bytes := 1.",
                       "Audit": "Definition double4_contract (bytes : nat) := bytes = 1.",
                       "Object": "From Ed25519Simd.Double4 Require Audit ObjectBytes.\n"
                                 "Definition assembled_double4_correct : True := I."}
            for name, source in modules.items():
                path = component / (name + ".v")
                path.write_text(source)
                subprocess.run(["coqc", *flags, str(path)], cwd=work, check=True)
            with self.assertRaises(subprocess.CalledProcessError) as rejected:
                proof_build.check_object(work, flags, "double4")
            self.assertEqual(rejected.exception.cmd[-1], "Double4/Checked.v")

    def test_reuse_checks_sources_objects_and_compiler(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout, prepared, audit = (root / name for name in ("checkout", "prepared", "audit"))
            files = {"machine/_CoqProject": b"-Q . Machine\nProbe.v\n",
                     "machine/Probe.v": b"Definition probe := 1.\n", "machine/Probe.vo": b"compiled"}
            for path, data in files.items():
                dest = (prepared if path.endswith(".vo") else checkout) / path
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)
            manifest = {"coqc": "test", "files": {p: hashlib.sha256(b).hexdigest() for p, b in files.items()}}
            (prepared / "shared.json").write_text(json.dumps(manifest))
            with patch.dict(os.environ, {proof_build.SHARED_ENV: str(prepared)}), \
                    patch.object(proof_build, "compiler_version", return_value="test") as version:
                def reuse():
                    proof_build.compile_libraries(audit, ("machine",), checkout)

                reuse()
                self.assertEqual({p: (audit / p).read_bytes() for p in files}, files)
                for path, data in files.items():
                    with self.subTest(path=path):
                        dest = (prepared if path.endswith(".vo") else checkout) / path
                        dest.write_bytes(data + b" ")
                        with self.assertRaisesRegex(ValueError, path):
                            reuse()
                        self.assertEqual((audit / "machine/Probe.vo").read_bytes(), files["machine/Probe.vo"])
                        dest.write_bytes(data)
                version.return_value = "other"
                with self.assertRaisesRegex(ValueError, "coqc"):
                    reuse()

    def test_failed_shared_build_can_be_retried(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "shared"
            with patch.object(proof_build.subprocess, "run", side_effect=OSError("build failed")):
                with self.assertRaisesRegex(OSError, "build failed"):
                    proof_build.prepare_shared_libraries(output, jobs=2)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
