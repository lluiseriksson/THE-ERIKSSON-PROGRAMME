#!/usr/bin/env python3
"""Fail-closed synthetic tests for the exact P0--P9 v56 evidence auditor."""

from __future__ import annotations

import io
import json
from pathlib import Path
import tarfile
import tempfile

import audit_p0_p9_v56_evidence as gate


def stage_output(stage: str, paths: list[str]) -> bytes:
    if stage == "head":
        return f"{gate.SOURCE_SHA}\n".encode()
    if stage == "mathlib_pin":
        return f"{gate.MATHLIB_SHA}\n".encode()
    if stage == "lean_version":
        return b"Lean (version 4.29.0-rc6, x86_64-unknown-linux-gnu)\n"
    if stage == "lake_version":
        return b"Lake version 5.0.0-src\n"
    if stage == "p0_p9_static_gate":
        return b"P0_P9_DIAGNOSTIC_STATIC_OK\n"
    if stage == "p0_p9_static_selftest":
        return b"P0_P9_DIAGNOSTIC_SELFTEST_OK\n"
    for index, source in enumerate(paths, start=1):
        if stage == gate.stage_for(index, source) and source in gate.AXIOM_COUNTS:
            return (
                "declaration depends on axioms: [propext, Quot.sound]\n"
                * gate.AXIOM_COUNTS[source]
            ).encode()
    return f"STAGE={stage} OK\n".encode()


def write_archive(
    destination: Path,
    *,
    mutate_log: str | None = None,
    drop_stage: str | None = None,
    forbidden_stage: str | None = None,
) -> None:
    paths = gate.exact_paths()
    stages = list(gate.BASE_WITH_APT + gate.exact_queue(paths))
    if drop_stage is not None:
        stages.remove(drop_stage)
    records: list[dict[str, object]] = []
    payloads: dict[str, bytes] = {}
    for index, stage in enumerate(stages):
        log_name = f"{index:03d}-{stage}.log"
        output = stage_output(stage, paths)
        if stage == forbidden_stage:
            output += b"declaration depends on axioms: [sorryAx]\n"
        records.append(
            {
                "stage": stage,
                "exit": 0,
                "log": log_name,
                "output_sha256": gate.sha256(output),
            }
        )
        payloads[f"{gate.EVIDENCE_ROOT}/{log_name}"] = output
    if mutate_log is not None:
        record = next(item for item in records if item["stage"] == mutate_log)
        payloads[f"{gate.EVIDENCE_ROOT}/{record['log']}"] += b"tampered\n"
    evidence = {
        "source_sha": gate.SOURCE_SHA,
        "runner_rev": gate.RUNNER_REV,
        "mathlib_sha": gate.MATHLIB_SHA,
        "status": "PASS",
        "records": records,
    }
    payloads[f"{gate.EVIDENCE_ROOT}/evidence.json"] = json.dumps(
        evidence, sort_keys=True
    ).encode()
    with tarfile.open(destination, "w:gz") as archive:
        for name, payload in sorted(payloads.items()):
            info = tarfile.TarInfo(name)
            info.size = len(payload)
            info.mtime = 0
            archive.addfile(info, io.BytesIO(payload))


def must_fail(path: Path, label: str) -> None:
    try:
        gate.audit(path)
    except ValueError:
        return
    raise AssertionError(f"{label} did not fail closed")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="p0-p9-v56-evidence-") as raw:
        root = Path(raw)
        positive = root / "positive.tar.gz"
        write_archive(positive)
        result = gate.audit(positive)
        if "P0_P9_V56_EVIDENCE_OK" not in result:
            raise AssertionError("positive archive did not pass")

        tampered = root / "tampered.tar.gz"
        write_archive(tampered, mutate_log="head")
        must_fail(tampered, "stage-log tamper")

        missing = root / "missing.tar.gz"
        write_archive(missing, drop_stage="p0_p9_p3_algebra_repro")
        must_fail(missing, "stage-order deletion")

        forbidden = root / "forbidden.tar.gz"
        paths = gate.exact_paths()
        source = next(path for path in paths if path in gate.AXIOM_COUNTS)
        stage = gate.stage_for(paths.index(source) + 1, source)
        write_archive(forbidden, forbidden_stage=stage)
        must_fail(forbidden, "forbidden axiom")

    print(
        "P0_P9_V56_EVIDENCE_SELFTEST_OK "
        "positive=pass hash_tamper=fail_closed stage_order=fail_closed "
        "forbidden_axiom=fail_closed"
    )


if __name__ == "__main__":
    main()
