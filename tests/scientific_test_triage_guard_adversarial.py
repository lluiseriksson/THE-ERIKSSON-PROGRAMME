#!/usr/bin/env python3
"""Executed attacks for the A/B/C scientific pytest triage guard."""

from __future__ import annotations

import ast
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.pytest_scientific_triage_guard import (
    CLASS_B,
    CLASS_C,
    _first_cause,
    evaluate,
    invalidate_result,
    load_manifest,
    validate_owner_decision_record,
)
from scripts.validate_scientific_triage_trigger_coverage import (
    CoverageError,
    derive_dependencies,
    load_manifest as load_coverage_manifest,
    trigger_match,
    verify_coverage,
    workflow_patterns,
)


MANIFEST_PATH = ROOT / ".github" / "scientific-test-triage.json"
SCRIPT = ROOT / "scripts" / "pytest_scientific_triage_guard.py"
TRIGGER_SCRIPT = ROOT / "scripts" / "validate_scientific_triage_trigger_coverage.py"
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
    with tempfile.TemporaryDirectory(prefix="scientific-triage-attack-") as directory:
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
    classified = manifest["classified_failures"]
    evidence_lost = [item for item in classified if item["class"] == CLASS_B]
    repairable = [item for item in classified if item["class"] == CLASS_C]
    evidence_nodeids = [item["nodeid"] for item in evidence_lost]
    repairable_nodeids = [item["nodeid"] for item in repairable]
    current_nodeids = evidence_nodeids + repairable_nodeids
    current_failures = evidence_lost + repairable
    base = inventory(repairable_nodeids, repairable)

    require(manifest["counts"] == {
        "A_VESTIGIAL": 0,
        "B_IRREPARABLE_EVIDENCE_LOST": 4,
        "C_REPAIRABLE_DEBT": 5,
    }, "TRIAGE_COUNTS: unexpected A/B/C partition")
    print("TRIAGE_COUNTS: PASS A=0 B=4 C=5 exit=0")

    owner_decision = manifest["owner_decision"]
    require(
        owner_decision["status"] == "DECIDED"
        and owner_decision["resolution"] == "quarantine"
        and owner_decision["record"]["pull_request"] == 59,
        "OWNER_DECISION: canonical E_DECIDED quarantine record is absent",
    )
    print(
        "OWNER_DECISION: PASS E_DECIDED=quarantine pr=59 "
        f"commit={owner_decision['record']['commit']} exit=0"
    )
    validate_owner_decision_record(ROOT, manifest)
    print(
        "OWNER_DECISION_RECORD: PASS blobs=2 inventory=319 "
        "class_B_nodeids=4 exit=0"
    )

    coverage_manifest = load_coverage_manifest(MANIFEST_PATH)
    dependencies = derive_dependencies(ROOT, coverage_manifest)
    triggers = workflow_patterns(WORKFLOW)
    coverage_rows = verify_coverage(dependencies, triggers)
    require(len(dependencies) == 5, "TRIGGER_COVERAGE: wrong class-C count")
    require(len(coverage_rows) >= 10, "TRIGGER_COVERAGE: missing test/import dependencies")
    for nodeid, paths in dependencies.items():
        script_paths = [path for path in paths if path.startswith("scripts/")]
        require(script_paths, f"TRIGGER_COVERAGE: no direct script import {nodeid}")
        for dependency in paths:
            for event, (mode, patterns) in triggers.items():
                covered, decisive = trigger_match(dependency, mode, patterns)
                require(covered, f"TRIGGER_COVERAGE: {event} bypass for {dependency}")
                print(
                    f"TRIGGER_CAUSAL: PASS nodeid={nodeid} dependency={dependency} "
                    f"event={event} pattern={decisive} exit=0"
                )
    broken_triggers = deepcopy(triggers)
    for event, (mode, patterns) in broken_triggers.items():
        broken_triggers[event] = (
            mode,
            [pattern for pattern in patterns if pattern != "scripts/**"],
        )
    try:
        verify_coverage(dependencies, broken_triggers)
    except CoverageError as exc:
        require("uncovered" in str(exc), "TRIGGER_COVERAGE_ATTACK: wrong first cause")
        print(f"TRIGGER_COVERAGE_ATTACK: FAIL first_cause={exc} exit=2")
    else:
        raise RuntimeError("TRIGGER_COVERAGE_ATTACK: missing scripts/** survived")

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
    check(
        "ATTACK_1_TENTH_FAILURE",
        manifest,
        base,
        inventory(current_nodeids + [tenth["nodeid"]], current_failures + [tenth]),
        "FAIL",
        1,
        "tenth",
    )

    swapped = evidence_lost + repairable[:-1] + [tenth]
    check(
        "ATTACK_2_SWAP_NODEID_KEEP_NINE",
        manifest,
        base,
        inventory(current_nodeids[:-1] + [tenth["nodeid"]], swapped),
        "FAIL",
        2,
        "did not execute",
    )

    collection = {"nodeid": "tests/broken.py", "phase": "collection", "first_cause": "SyntaxError", "cause_sha256": "collection"}
    check("ATTACK_3_COLLECTION_ERROR", manifest, base, inventory(current_nodeids, current_failures, errors=[collection], exit_code=1), "FAIL", 2, "collection error")
    check("ATTACK_3_TIMEOUT", manifest, base, inventory(current_nodeids, current_failures, timed_out=True, exit_code=124), "FAIL", 2, "timed out")

    repaired = repairable[:-1]
    check(
        "ATTACK_4_ONE_C_REPAIRED",
        manifest,
        base,
        inventory(current_nodeids, evidence_lost + repaired),
        "PASS",
        0,
        "quarantined evidence loss plus repairable debt only",
    )
    check(
        "ATTACK_5_C_REINTRODUCTION",
        manifest,
        inventory(repairable_nodeids, repaired),
        inventory(current_nodeids, current_failures),
        "FAIL",
        1,
        "ee5fb3",
    )
    selector = "CHANGE_BASE: ${{ github.event.before || github.event.pull_request.base.sha }}"
    require(
        selector in WORKFLOW.read_text(encoding="utf-8"),
        "ATTACK_5_BASE_RATCHET: workflow does not select the prior exact PR head",
    )
    print("ATTACK_5_BASE_RATCHET: PASS first_cause=prior-exact-head exit=0")

    decision, code = evaluate(manifest, base, inventory(current_nodeids, current_failures))
    require(decision["status"] == "PASS" and code == 0, "B_VISIBILITY: baseline rejected")
    require(len(decision["evidence_loss_active"]) == 4, "B_VISIBILITY: active B set hidden")
    require(len(decision["repairable_debt"]) == 5, "B_VISIBILITY: C debt count wrong")
    require(
        decision["owner_decision"] == owner_decision,
        "B_VISIBILITY: decided quarantine record hidden or changed",
    )
    print("B_VISIBILITY: PASS active_B=4 repairable_C=5 owner_decision=E_DECIDED:quarantine exit=0")

    decision, code = evaluate(manifest, base, inventory(current_nodeids, repairable))
    require(decision["status"] == "PASS" and code == 0, "B_INACTIVE: passing B rejected")
    require(len(decision["evidence_loss_inactive"]) == 4, "B_INACTIVE: inactive B set hidden")
    print("B_INACTIVE: PASS inactive_B=4 owner_decision=E_DECIDED:quarantine exit=0")

    changed_b = dict(evidence_lost[0])
    changed_b["first_cause"] = "AssertionError: changed evidence-loss symptom"
    changed_b["cause_sha256"] = "changed"
    check(
        "B_CAUSE_DRIFT",
        manifest,
        base,
        inventory(current_nodeids, [changed_b] + evidence_lost[1:] + repairable),
        "FAIL",
        1,
        "changed evidence-loss symptom",
    )

    with tempfile.TemporaryDirectory(prefix="stale-result-") as directory:
        stale = Path(directory) / "decision.json"
        stale.write_text('{"status":"PASS"}\n', encoding="utf-8")
        invalidate_result(stale)
        require(not stale.exists(), "ATTACK_6 stale PASS survived invalidation")
        print("ATTACK_6_STALE_PASS: ABSENT first_cause=invalidated exit=0")

    trees = [
        ast.parse(path.read_text(encoding="utf-8"))
        for path in (SCRIPT, TRIGGER_SCRIPT)
    ]
    require(
        not any(
            isinstance(node, ast.Assert)
            for tree in trees
            for node in ast.walk(tree)
        ),
        "ATTACK_7 decisive assert found",
    )
    print(f"ATTACK_7_OPTIMIZATION: PASS first_cause=no-assert optimize={sys.flags.optimize} exit=0")

    with tempfile.TemporaryDirectory(prefix="manifest-attacks-") as directory:
        missing = Path(directory) / "missing.json"
        corrupt = Path(directory) / "corrupt.json"
        corrupt.write_text("{broken", encoding="utf-8")
        early_failure_attack(missing, "HEAD", "ATTACK_8_MISSING_MANIFEST")
        early_failure_attack(corrupt, "HEAD", "ATTACK_8_CORRUPT_MANIFEST")
        early_failure_attack(MANIFEST_PATH, "0" * 40, "ATTACK_8_UNRESOLVABLE_BASE")
        decision_drift = Path(directory) / "decision-drift.json"
        drifted = deepcopy(manifest)
        drifted["owner_decision"]["record"]["sha256"] = "0" * 64
        decision_drift.write_text(json.dumps(drifted), encoding="utf-8")
        early_failure_attack(
            decision_drift,
            "HEAD",
            "OWNER_DECISION_RECORD_DRIFT",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
