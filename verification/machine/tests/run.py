#!/usr/bin/env python3
"""Run a corpus against the Coq model, Intel XED, and/or a native x86-64 CPU."""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import subprocess
import tempfile

from case_data import REGISTER_IDS, campaign, registers, validate
from model.backend import Model
from overflow import overflow_cases
from xed import backend as xed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROBE_INPUTS = {"control": "input_rcx", "mixed": "seeds", "prologue": "seeds", "aligned": "seeds"}


def jsonl(path):
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if line.strip():
            try:
                yield json.loads(line)
            except ValueError as exc:
                raise ValueError(f"{path}:{line_no}: {exc}") from exc


def source_digest(root, paths):
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(str(path.relative_to(root)).encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def corpus_digest(cases):
    digest = hashlib.sha256()
    for case in cases:
        digest.update(json.dumps(case, sort_keys=True, separators=(",", ":")).encode() + b"\n")
    return digest.hexdigest()


def complete_case(case, encoded):
    """Freeze defaults as well as explicit inputs so replay needs no generator."""
    result = {**case, "registers": {str(i): v for i, v in enumerate(registers(case))}}
    if encoded is not None:
        result["bytes"] = encoded.hex()
    return result


def replay_cases(record):
    if "case" in record:
        return [record["case"]]  # Includes legacy failure records.
    if record.get("schema_version") != 2 or not record.get("checked"):
        raise ValueError("this report does not retain replayable case inputs")
    cases = record["checked"]
    for case in cases:
        validate(case)
        if set(case.get("registers", {})) != REGISTER_IDS or "bytes" not in case:
            raise ValueError("incomplete case inputs in report")
    if corpus_digest(cases) != record.get("corpus_sha256"):
        raise ValueError("report corpus SHA-256 mismatch")
    return cases


def cpu_info():
    path = Path("/proc/cpuinfo")
    if not path.exists():
        return {}
    allowed = os.sched_getaffinity(0) if hasattr(os, "sched_getaffinity") else None
    for entry in path.read_text().strip().split("\n\n"):
        fields = dict((k.strip(), v.strip()) for k, v in
                      (line.split(":", 1) for line in entry.splitlines() if ":" in line))
        if allowed is None or int(fields.get("processor", -1)) in allowed:
            return fields
    return {}


def write_json(path, record):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as f:
        json.dump(record, f, indent=2)
        f.write("\n")
    os.replace(f.name, path)


def inputs(args):
    if args.replay:
        yield from replay_cases(args.record)
        return
    for path in args.cases or sorted((HERE / "cases").glob("*.jsonl")):
        yield from jsonl(path)
    if not args.cases:
        yield from overflow_cases()
    yield from campaign(args.seed, args.random)


def mismatch(path, info, case, stage, prediction, encoded, expected, observed):
    model_bytes, result = prediction
    full_case = complete_case(case, encoded)
    write_json(path, {**info, "case": full_case, "stage": stage,
                      "coq_bytes": model_bytes.hex() if model_bytes is not None else None,
                      "coq_destination": result, "expected": expected, "observed": observed})
    raise ValueError(f"{case['id']}: {stage} mismatch; replay record: {path}")


def check_probe(name, args, work, model, info):
    from native.backend import execute_probe

    key = f"{name}_probe"
    field = PROBE_INPUTS[name]
    recorded = args.record.get(key, {})
    encoded, rows = model.block_probe(name, recorded.get(field))
    inputs = [row[0] for row in rows]
    probe = {"bytes": encoded.hex(), field: inputs}
    expected = {"bytes": encoded.hex(), "rows": rows}
    if recorded and probe != recorded:
        observed, expected = probe, recorded
    else:
        observed = execute_probe(name, work, encoded, inputs, int(info["cpu"]["processor"]))
    if observed != expected:
        write_json(args.failure, {**info, key: recorded or probe, "probe": name, "stage": "block execution",
                                  "expected": expected, "observed": observed})
        raise ValueError(f"{name} probe mismatch; replay record: {args.failure}")
    info[key] = probe


def run(args, work):
    cases = []
    seen = set()
    selected_probe = args.probe
    if args.replay and "case" not in args.record and "checked" not in args.record:
        # Old control-flow failure records predate the explicit probe name.
        selected_probe = args.record.get("probe", "control")
        if selected_probe not in PROBE_INPUTS or f"{selected_probe}_probe" not in args.record:
            raise ValueError("unrecognized block-probe replay record")
    for case in (() if selected_probe else inputs(args)):
        if args.case and case["id"] != args.case:
            continue
        validate(case)
        if case["id"] in seen:
            raise ValueError(f"duplicate case id {case['id']}")
        seen.add(case["id"])
        cases.append(case)
    if not cases and not selected_probe:
        raise ValueError("no matching cases")
    cpu = cpu_info()
    harness = [p for p in HERE.rglob("*") if p.is_file() and p.suffix in (".py", ".c", ".S", ".sh")]
    harness.append(ROOT.parent / "proof_build.py")
    info = {"schema_version": 2, "backend": args.backend,
            "model_sha256": source_digest(ROOT, [ROOT / "_CoqProject", *ROOT.rglob("*.v")]),
            "harness_sha256": source_digest(ROOT.parent, harness),
            "campaign_seeds": sorted({c["campaign_seed"] for c in cases if "campaign_seed" in c}),
            "export_seeds": sorted({c["export_seed"] for c in cases if "export_seed" in c}),
            "cpu": {k: cpu.get(k) for k in ("processor", "model name", "vendor_id", "microcode")},
            "platform": platform.platform(), "python": sys.version,
            "coq": subprocess.check_output(["coqc", "--version"], text=True).strip()}

    check_xed = not selected_probe and args.backend in ("all", "xed")
    check_native = args.backend in ("all", "native")
    if check_xed and not args.xed_kit:
        raise ValueError("set XED_KIT or pass --xed-kit for the XED backend")
    if check_native:
        from native.backend import Native, require_host
        require_host(cpu)
    elif selected_probe:
        raise ValueError("standalone block probes require the native or all backend")
    if check_native or check_xed:
        info["cc"] = subprocess.check_output(["cc", "--version"], text=True).strip()

    model = Model(ROOT, work / "model")
    if selected_probe:
        info["probe"] = selected_probe
        check_probe(selected_probe, args, work, model, info)
        if args.report:
            write_json(args.report, info)
        print(f"{selected_probe} block probe passed")
        return
    predictions = list(model.predict(cases))
    encodings = []
    for case, prediction in zip(cases, predictions):
        model_bytes, result = prediction
        encoded = bytes.fromhex(case["bytes"]) if "bytes" in case else model_bytes
        if model_bytes is None:
            mismatch(args.failure, info, case, "encodable", prediction, encoded, True, False)
        if model_bytes != encoded:
            mismatch(args.failure, info, case, "linked or recorded bytes", prediction, encoded,
                     encoded.hex(), model_bytes.hex())
        if "expected" in case and result != case["expected"]:
            mismatch(args.failure, info, case, "fixed destination", prediction, encoded, case["expected"], result)
        encodings.append(encoded)

    if check_xed:
        info["xed_library_sha256"] = hashlib.sha256((args.xed_kit / "lib/libxed.a").read_bytes()).hexdigest()
        decoded = xed.decode(args.xed_kit, work, encodings)
        for case, prediction, encoded, observed in zip(cases, predictions, encodings, decoded):
            wanted = xed.expected(case["instruction"], len(encoded))
            if observed != wanted:
                mismatch(args.failure, info, case, "XED decode", prediction, encoded, wanted, observed)
    if check_native:
        probes = []
        if args.replay and "checked" in args.record and not args.case:
            probes = [name for name in PROBE_INPUTS if f"{name}_probe" in args.record]
        elif not (args.cases or args.case or args.replay):
            probes = PROBE_INPUTS
        for name in probes:
            check_probe(name, args, work, model, info)
        native = Native(work, (case["instruction"] for case in cases), int(cpu["processor"]))
        for case, prediction, encoded in zip(cases, predictions, encodings):
            wanted = registers(case)
            wanted[case["instruction"][1]] = prediction[1]
            observed = native.execute(case, encoded)
            if observed.get("registers") != wanted:
                mismatch(args.failure, info, case, "native execution", prediction, encoded,
                         {"registers": wanted}, observed)

    info.update(cases=len(cases), forms=dict(Counter(case["instruction"][0] for case in cases)))
    if args.report:
        checked = [complete_case(case, encoded) for case, encoded in zip(cases, encodings)]
        info["corpus_sha256"] = corpus_digest(checked)
        info["checked"] = checked
        write_json(args.report, info)
    print(f"{len(cases)} cases passed ({args.backend}); {len(info['forms'])} instruction forms")
    for name, field in PROBE_INPUTS.items():
        probe = info.get(f"{name}_probe")
        if probe:
            print(f"{name} block probe passed for {len(probe[field])} inputs")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--backend", choices=["model", "xed", "native", "all"], help="defaults to all, or the recorded backend for replay")
    source = p.add_mutually_exclusive_group()
    source.add_argument("--cases", type=Path, action="append", help="use this JSONL corpus (repeatable)")
    source.add_argument("--replay", type=Path, help="replay a failure record or a report containing complete inputs")
    source.add_argument("--probe", choices=PROBE_INPUTS, help="run one mnemonic block probe against the CPU")
    p.add_argument("--case", help="select one case by id")
    p.add_argument("--seed", type=int, default=1, help="seed for --random; imported inputs retain their own seeds")
    p.add_argument("--random", type=int, default=0, metavar="COUNT")
    p.add_argument("--xed-kit", type=Path, default=os.environ.get("XED_KIT"))
    p.add_argument("--failure", type=Path, help="destination for a replayable mismatch record")
    p.add_argument("--report", type=Path, help="write complete replayable inputs, coverage and run metadata as JSON")
    args = p.parse_args()
    if args.probe and (args.case or args.random):
        p.error("--probe selects a block program and cannot be combined with vector case selection")
    if args.random < 0 or (args.replay and args.random):
        p.error("--random requires a nonnegative count and a corpus run")
    if args.failure is None:
        args.failure = (args.replay.with_suffix(".replay.json") if args.replay
                        else Path("machine-failure.json"))
    if args.replay and args.replay.resolve() == args.failure.resolve():
        p.error("choose a failure output distinct from the original replay record")
    try:
        args.record = json.loads(args.replay.read_text()) if args.replay else {}
        args.backend = args.backend or args.record.get("backend", "all")
        if args.backend not in ("all", "model", "xed", "native"):
            raise ValueError("unrecognized backend in replay record")
        with tempfile.TemporaryDirectory(prefix="machine-conformance-") as tmp:
            run(args, Path(tmp))
    except (KeyError, ValueError, OSError) as exc:
        sys.exit(str(exc))


if __name__ == "__main__":
    main()
