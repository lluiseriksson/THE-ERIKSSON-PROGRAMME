#!/usr/bin/env python3
"""Synthetic positive/tamper tests for the durable P0--P9 GitHub auditor."""

from __future__ import annotations

import io
import json
from pathlib import Path
import tarfile
import tempfile
import zipfile

import audit_p0_p9_v56_github_evidence as gate
import github_p0_p9_v56_driver as contract


def output_for(stage: str, expected: int | None) -> str:
    if stage == "p0_p9_static_gate":
        return "P0_P9_DIAGNOSTIC_STATIC_OK\n"
    if stage == "p0_p9_static_selftest":
        return "P0_P9_DIAGNOSTIC_SELFTEST_OK\n"
    if expected is not None:
        return "decl depends on axioms: [propext, Quot.sound]\n" * expected
    return f"STAGE={stage} OK\n"


def write_fixture(
    destination: Path, *, forbidden_axiom: bool = False,
    checkpoint_drift: bool = False, outer_tamper: bool = False
) -> None:
    repo = Path(__file__).resolve().parents[1]
    paths = contract.exact_paths(repo)
    queue = contract.queue(paths)
    files: dict[str, bytes] = {
        "evidence/checkpoint.txt": (
            f"SOURCE_SHA={contract.SOURCE_SHA}\n"
            f"ACTUAL_SOURCE_HEAD={contract.SOURCE_SHA}\n"
            f"CONTROL_SHA={gate.CONTROL_SHA}\n"
            f"GITHUB_SHA={gate.CONTROL_SHA if not checkpoint_drift else '0' * 40}\n"
            "COLD_MODE=true\n"
        ).encode(),
        "evidence/control-driver.sha256": (
            f"{gate.DRIVER_SHA256.lower()}  {gate.DRIVER_PATH}\n"
        ).encode(),
        "evidence/toolchain.txt": (
            "Lean (version 4.29.0-rc6, x86_64-unknown-linux-gnu)\n"
            "Lake version 5.0.0-src\n"
        ).encode(),
        "evidence/lake-update.log": b"lake update OK\n",
        "evidence/mathlib.txt": f"MATHLIB_SHA={contract.MATHLIB_SHA}\n".encode(),
        "evidence/cache-get.log": b"cache OK\n",
    }
    records: list[dict[str, object]] = []
    axioms: dict[str, list[list[str]]] = {}
    forbidden_used = False
    for stage, _, expected in queue:
        output = output_for(stage, expected)
        if expected is not None and forbidden_axiom and not forbidden_used:
            output = output.replace("Quot.sound", "sorryAx", 1)
            forbidden_used = True
        payload = output.encode()
        log_name = f"{stage}.log"
        files[f"evidence/{log_name}"] = payload
        records.append(
            {
                "stage": stage,
                "exit": 0,
                "seconds": 1.0,
                "log": log_name,
                "output_sha256": gate.sha256(payload),
            }
        )
        if expected is not None:
            if forbidden_axiom and forbidden_used and stage not in axioms:
                # Preserve the serialized shape; the independent log parser is
                # expected to reject the forbidden name before comparing it.
                axioms[stage] = [["propext", "sorryAx"]] + [
                    ["Quot.sound", "propext"] for _ in range(expected - 1)
                ]
            else:
                axioms[stage] = [
                    ["Quot.sound", "propext"] for _ in range(expected)
                ]
    evidence = {
        "source_sha": contract.SOURCE_SHA,
        "mathlib_sha": contract.MATHLIB_SHA,
        "status": "PASS",
        "first_error": None,
        "records": records,
        "axiom_headers": sum(contract.AXIOM_COUNTS.values()),
    }
    files["evidence/evidence.json"] = (
        json.dumps(evidence, sort_keys=True, indent=2) + "\n"
    ).encode()
    files["evidence/axioms.json"] = (
        json.dumps(axioms, sort_keys=True, indent=2) + "\n"
    ).encode()
    files["evidence/FINAL_STATUS"] = b"FINAL_STATUS=PASS\n"
    sums = "".join(
        f"{gate.sha256(payload)}  {name}\n"
        for name, payload in sorted(files.items())
    ).encode()
    files["evidence/SHA256SUMS"] = sums

    tar_buffer = io.BytesIO()
    with tarfile.open(fileobj=tar_buffer, mode="w:gz") as archive:
        for name, payload in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size = len(payload)
            info.mtime = 0
            archive.addfile(info, io.BytesIO(payload))
    inner = tar_buffer.getvalue()
    outer = dict(files)
    outer[gate.ARCHIVE_NAME] = inner
    outer["evidence/ARCHIVE_SHA256"] = (
        f"{gate.sha256(inner)}  {gate.ARCHIVE_NAME}\n"
    ).encode()
    if outer_tamper:
        outer["evidence/p0_p9_static_gate.log"] += b"tampered\n"
    with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, payload in sorted(outer.items()):
            archive.writestr(name, payload)


def must_fail(path: Path, label: str) -> None:
    try:
        gate.audit(path)
    except ValueError:
        return
    raise AssertionError(f"{label} did not fail closed")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="p0-p9-github-evidence-") as raw:
        root = Path(raw)
        positive = root / "positive.zip"
        write_fixture(positive)
        result = gate.audit(positive)
        if gate.RESULT_MARKER not in result:
            raise AssertionError("positive fixture did not pass")
        tampered = root / "tampered.zip"
        write_fixture(tampered, outer_tamper=True)
        must_fail(tampered, "outer/inner tamper")
        forbidden = root / "forbidden.zip"
        write_fixture(forbidden, forbidden_axiom=True)
        must_fail(forbidden, "forbidden axiom")
        identity = root / "identity.zip"
        write_fixture(identity, checkpoint_drift=True)
        must_fail(identity, "checkpoint drift")
    print(
        f"{gate.RESULT_MARKER}_SELFTEST_OK positive=pass "
        "byte_tamper=fail_closed forbidden_axiom=fail_closed "
        "checkpoint_drift=fail_closed"
    )


if __name__ == "__main__":
    main()
