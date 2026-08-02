#!/usr/bin/env python3
"""Executed attacks for the nominal scientific-test debt quarantine."""

from __future__ import annotations

import ast
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.pytest_nominal_debt_guard import (
    _first_cause,
    evaluate,
    invalidate_result,
    load_manifest,
)


MANIFEST_PATH = ROOT / ".github" / "scientific-test-debt-baseline.json"
SCRIPT = ROOT / "scripts" / "pytest_nominal_debt_guard.py"
WORKFLOW = ROOT / ".github" / "workflows" / "control-plane.yml"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def inventory(collected, failures, *, errors=None, timed_out=False, exit_code=None):
    return {
        "schema": "pytest-failure-inventory/v1",
        "collected": list(collected),
        "failures": list(failures),
        "collection_errors": list(errors or []),
        "timed_out": timed_out,
        "pytest_exit": (1 if failures else 0) if exit_code is None else exit_code,
    }


def check(name: str, manifest, base, current, expected_status: str, expected_exit: int, cause: str) -> None:
    decision, code = evaluate(manifest, base, current)
    require(decision["status"] == expected_status, f"{name}: status {decision['status']}")
    require(code == expected_exit, f"{name}: exit {code}")
    require(cause in decision["first_cause"], f"{name}: cause {decision['first_cause']}")
    print(f"{name}: {decision['status']} first_cause={decision['first_cause']} exit={code}")


def early_failure_attack(manifest_arg: Path, base_sha: str, label: str) -> None:
    with tempfile.TemporaryDirectory(prefix="nominal-debt-attack-") as directory:
        result = Path(directory) / "decision.json"
        result.write_text('{"status":"PASS"}\n', encoding="utf-8")
        command = [sys.executable]
        if sys.flags.optimize:
            command.append("-O")
        command.extend(
            [
                str(SCRIPT),
                "--manifest",
                str(manifest_arg),
                "--result",
                str(result),
                "--comparison-base",
                base_sha,
                "--repo",
                str(ROOT),
            ]
        )
        completed = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require(completed.returncode == 2, f"{label}: exit {completed.returncode}")
        decision = json.loads(result.read_text(encoding="utf-8"))
        require(decision["status"] == "FAIL", f"{label}: stale PASS survived")
        require("PASS" not in result.read_text(encoding="utf-8"), f"{label}: PASS token survived")
        print(f"{label}: FAIL first_cause={decision['first_cause']} exit={completed.returncode}")


def main() -> int:
    manifest = load_manifest(MANIFEST_PATH)
    known = manifest["known_failures"]
    nodeids = [item["nodeid"] for item in known]
    base = inventory(nodeids, known)

    multiline = SimpleNamespace(
        longrepr=SimpleNamespace(
            reprcrash=SimpleNamespace(
                message="AssertionError: stable first cause\n  pytest-rendered diff"
            )
        )
    )
    require(
        _first_cause(multiline) == "AssertionError: stable first cause",
        "FIRST_CAUSE_NORMALIZATION: multiline renderer detail changed the fingerprint",
    )
    print("FIRST_CAUSE_NORMALIZATION: PASS first_cause=stable-first-line exit=0")

    tenth = {
        "nodeid": "tests/test_new_regression.py::test_tenth",
        "phase": "call",
        "first_cause": "AssertionError: tenth",
        "cause_sha256": "new",
    }
    check("ATTACK_1_TENTH_FAILURE", manifest, base, inventory(nodeids + [tenth["nodeid"]], known + [tenth]), "FAIL", 1, "tenth")

    swapped = known[:-1] + [tenth]
    check("ATTACK_2_SWAP_NODEID_KEEP_NINE", manifest, base, inventory(nodeids[:-1] + [tenth["nodeid"]], swapped), "FAIL", 2, "did not execute")

    collection = {"nodeid": "tests/broken.py", "phase": "collection", "first_cause": "SyntaxError", "cause_sha256": "collection"}
    check("ATTACK_3_COLLECTION_ERROR", manifest, base, inventory(nodeids, known, errors=[collection], exit_code=1), "FAIL", 2, "collection error")
    check("ATTACK_3_TIMEOUT", manifest, base, inventory(nodeids, known, timed_out=True, exit_code=124), "FAIL", 2, "timed out")

    repaired = known[:-1]
    repaired_ids = nodeids[:-1]
    check("ATTACK_4_ONE_REPAIRED", manifest, base, inventory(nodeids, repaired), "PASS", 0, "nominal debt only")
    check("ATTACK_5_REINTRODUCTION", manifest, inventory(nodeids, repaired), inventory(nodeids, known), "FAIL", 1, "ee5fb3")
    selector = "CHANGE_BASE: ${{ github.event.before || github.event.pull_request.base.sha }}"
    require(
        selector in WORKFLOW.read_text(encoding="utf-8"),
        "ATTACK_5_BASE_RATCHET: workflow does not select the prior exact PR head",
    )
    print("ATTACK_5_BASE_RATCHET: PASS first_cause=prior-exact-head exit=0")

    with tempfile.TemporaryDirectory(prefix="stale-result-") as directory:
        stale = Path(directory) / "decision.json"
        stale.write_text('{"status":"PASS"}\n', encoding="utf-8")
        invalidate_result(stale)
        require(not stale.exists(), "ATTACK_6 stale PASS survived invalidation")
        print("ATTACK_6_STALE_PASS: ABSENT first_cause=invalidated exit=0")

    tree = ast.parse(SCRIPT.read_text(encoding="utf-8"))
    require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)), "ATTACK_7 decisive assert found")
    print(f"ATTACK_7_OPTIMIZATION: PASS first_cause=no-assert optimize={sys.flags.optimize} exit=0")

    with tempfile.TemporaryDirectory(prefix="manifest-attacks-") as directory:
        missing = Path(directory) / "missing.json"
        corrupt = Path(directory) / "corrupt.json"
        corrupt.write_text("{broken", encoding="utf-8")
        early_failure_attack(missing, "HEAD", "ATTACK_8_MISSING_MANIFEST")
        early_failure_attack(corrupt, "HEAD", "ATTACK_8_CORRUPT_MANIFEST")
        early_failure_attack(MANIFEST_PATH, "0" * 40, "ATTACK_8_UNRESOLVABLE_BASE")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
