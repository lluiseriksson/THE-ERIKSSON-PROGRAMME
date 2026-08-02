#!/usr/bin/env python3
"""Fail-closed pytest triage for measured scientific failures.

Pytest still reports every scientific failure as FAILED.  This controller only
decides the CI exit status after comparing the structured failure inventory
with a versioned A/B/C classification and the exact comparison-base result.
Only class C is repairable debt.  Class B remains a separately visible
evidence-loss set pending owner decision E.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any


SCHEMA = "pytest-scientific-triage/v1"
REPORT_SCHEMA = "pytest-failure-inventory/v1"
DECISION_SCHEMA = "pytest-scientific-triage-decision/v1"
CLASS_A = "A_VESTIGIAL"
CLASS_B = "B_IRREPARABLE_EVIDENCE_LOST"
CLASS_C = "C_REPAIRABLE_DEBT"
CLASSES = (CLASS_A, CLASS_B, CLASS_C)
_inventory: dict[str, Any] = {
    "schema": REPORT_SCHEMA,
    "collected": [],
    "failures": [],
    "collection_errors": [],
}


def _first_cause(report: Any) -> str:
    def first_nonempty_line(value: Any) -> str:
        return next(
            (line.strip() for line in str(value).splitlines() if line.strip()),
            "",
        )

    longrepr = report.longrepr
    reprcrash = getattr(longrepr, "reprcrash", None)
    if reprcrash is not None:
        message = first_nonempty_line(getattr(reprcrash, "message", ""))
        if message:
            return message
    if isinstance(longrepr, tuple) and len(longrepr) >= 3:
        message = first_nonempty_line(longrepr[2])
        if message:
            return message
    lines = [line.strip() for line in str(longrepr).splitlines() if line.strip()]
    for line in reversed(lines):
        if line.startswith("E ") or line.startswith("E\t"):
            return line[1:].strip()
    return lines[-1] if lines else "unavailable failure cause"


def _failure_record(report: Any) -> dict[str, str]:
    cause = _first_cause(report)
    phase = str(getattr(report, "when", "collection"))
    return {
        "nodeid": str(getattr(report, "nodeid", "<unknown>")),
        "phase": phase,
        "first_cause": cause,
        "cause_sha256": hashlib.sha256((phase + "\0" + cause).encode("utf-8")).hexdigest(),
    }


def pytest_collection_finish(session: Any) -> None:
    _inventory["collected"] = [item.nodeid for item in session.items]


def pytest_runtest_logreport(report: Any) -> None:
    if report.failed:
        _inventory["failures"].append(_failure_record(report))


def pytest_collectreport(report: Any) -> None:
    if report.failed:
        _inventory["collection_errors"].append(_failure_record(report))


def pytest_sessionfinish(session: Any, exitstatus: int) -> None:
    report_path = os.environ.get("PYTEST_TRIAGE_REPORT")
    if not report_path:
        return
    _inventory["pytest_exit"] = int(exitstatus)
    _inventory["tests_collected"] = len(session.items)
    Path(report_path).write_text(
        json.dumps(_inventory, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def invalidate_result(path: Path) -> None:
    try:
        path.unlink(missing_ok=True)
    except OSError as exc:
        raise RuntimeError(f"cannot invalidate prior decision: {exc}") from exc
    if path.exists():
        raise RuntimeError("prior decision survived invalidation")


def load_manifest(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"manifest unavailable or corrupt: {exc}") from exc
    if not isinstance(data, dict) or data.get("schema") != SCHEMA:
        raise RuntimeError("manifest schema mismatch")
    failures = data.get("classified_failures")
    refs = data.get("measured_refs")
    counts = data.get("counts")
    owner_decision = data.get("owner_decision")
    if not isinstance(failures, list) or len(failures) != 9:
        raise RuntimeError("classification must contain exactly nine measured failures")
    if not isinstance(refs, list) or len(refs) != 6:
        raise RuntimeError("manifest must contain exactly six measured refs")
    if not isinstance(counts, dict) or set(counts) != set(CLASSES):
        raise RuntimeError("classification counts are absent or malformed")
    if (
        not isinstance(owner_decision, dict)
        or owner_decision.get("id") != "E"
        or owner_decision.get("scope") != CLASS_B
        or owner_decision.get("status") != "UNDECIDED"
    ):
        raise RuntimeError("evidence-loss owner decision E is absent or malformed")
    nodeids: set[str] = set()
    actual_counts = {name: 0 for name in CLASSES}
    for item in failures:
        if not isinstance(item, dict):
            raise RuntimeError("classification entry is not an object")
        required = (
            "class",
            "nodeid",
            "phase",
            "first_cause",
            "cause_sha256",
            "document_or_input",
            "disposition",
        )
        if any(not isinstance(item.get(key), str) or not item[key] for key in required):
            raise RuntimeError("classification entry is incomplete")
        if item["class"] not in CLASSES:
            raise RuntimeError(f"unknown triage class for {item['nodeid']}")
        if item["nodeid"] in nodeids:
            raise RuntimeError("classification contains a duplicate nodeid")
        nodeids.add(item["nodeid"])
        actual_counts[item["class"]] += 1
        expected = hashlib.sha256(
            (item["phase"] + "\0" + item["first_cause"]).encode("utf-8")
        ).hexdigest()
        if expected != item["cause_sha256"]:
            raise RuntimeError(f"classification cause hash mismatch for {item['nodeid']}")
    if counts != actual_counts:
        raise RuntimeError(
            f"classification counts mismatch: declared {counts}, actual {actual_counts}"
        )
    for ref in refs:
        if not isinstance(ref, dict) or not isinstance(ref.get("sha"), str):
            raise RuntimeError("measured ref entry is incomplete")
    return data


def _class_items(manifest: dict[str, Any], class_name: str) -> list[dict[str, Any]]:
    return [
        item
        for item in manifest["classified_failures"]
        if item["class"] == class_name
    ]


def _key(item: dict[str, Any]) -> tuple[str, str, str, str]:
    return (
        str(item.get("nodeid")),
        str(item.get("phase")),
        str(item.get("first_cause")),
        str(item.get("cause_sha256")),
    )


def evaluate(
    manifest: dict[str, Any], base: dict[str, Any], current: dict[str, Any]
) -> tuple[dict[str, Any], int]:
    vestigial = {_key(item): item for item in _class_items(manifest, CLASS_A)}
    evidence_lost = {_key(item): item for item in _class_items(manifest, CLASS_B)}
    repairable = {_key(item): item for item in _class_items(manifest, CLASS_C)}
    base_nodeids = [item["nodeid"] for item in _class_items(manifest, CLASS_C)]
    current_nodeids = [
        item["nodeid"]
        for item in manifest["classified_failures"]
        if item["class"] != CLASS_A
    ]
    first_cause = ""
    regressions: list[dict[str, Any]] = []

    for label, report in (("comparison base", base), ("current", current)):
        if report.get("timed_out"):
            first_cause = f"{label} pytest timed out"
            regressions.append({"kind": "timeout", "where": label})
            break
        errors = report.get("collection_errors")
        if not isinstance(errors, list):
            first_cause = f"{label} inventory is missing collection status"
            regressions.append({"kind": "invalid inventory", "where": label})
            break
        if errors:
            first_cause = f"{label} collection error: {errors[0].get('first_cause', 'unknown')}"
            regressions.extend({"kind": "collection error", "where": label, **err} for err in errors)
            break
        if report.get("pytest_exit") not in (0, 1):
            first_cause = f"{label} pytest exit {report.get('pytest_exit')} is not a test verdict"
            regressions.append({"kind": "pytest exit", "where": label, "exit": report.get("pytest_exit")})
            break
        collected = report.get("collected")
        if not isinstance(collected, list):
            first_cause = f"{label} inventory is missing collected nodeids"
            regressions.append({"kind": "invalid inventory", "where": label})
            break
        expected_nodeids = base_nodeids if label == "comparison base" else current_nodeids
        missing = [nodeid for nodeid in expected_nodeids if nodeid not in collected]
        if missing:
            first_cause = f"{label} did not execute classified nodeid {missing[0]}"
            regressions.extend({"kind": "test not executed", "where": label, "nodeid": nodeid} for nodeid in missing)
            break
        if label == "current":
            vestigial_collected = [
                item["nodeid"]
                for item in vestigial.values()
                if item["nodeid"] in collected
            ]
            if vestigial_collected:
                first_cause = f"vestigial nodeid is still collected: {vestigial_collected[0]}"
                regressions.extend(
                    {"kind": "vestigial test still collected", "nodeid": nodeid}
                    for nodeid in vestigial_collected
                )
                break

    if regressions:
        return _decision("FAIL", first_cause, base, current, [], [], [], [], regressions), 2

    base_failures = base.get("failures")
    current_failures = current.get("failures")
    if not isinstance(base_failures, list) or not isinstance(current_failures, list):
        return _decision("FAIL", "failure inventory is missing", base, current, [], [], [], [], [{"kind": "invalid inventory"}]), 2
    base_keys = [_key(item) for item in base_failures]
    current_keys = [_key(item) for item in current_failures]
    if len(set(base_keys)) != len(base_keys) or len(set(current_keys)) != len(current_keys):
        return _decision("FAIL", "duplicate failure report", base, current, [], [], [], [], [{"kind": "duplicate failure"}]), 2

    for item in base_failures:
        if _key(item) not in repairable:
            regressions.append({"kind": "comparison-base drift", **item})
    active = set(base_keys)
    for item in current_failures:
        key = _key(item)
        if key in evidence_lost:
            continue
        if key in repairable:
            if key not in active:
                regressions.append({"kind": "reintroduced repaired C failure", **item})
            continue
        if key in vestigial:
            regressions.append({"kind": "vestigial A failure remains", **item})
            continue
        regressions.append({"kind": "new or changed failure", **item})
    if regressions:
        cause = regressions[0].get("first_cause") or regressions[0]["kind"]
        return _decision("FAIL", str(cause), base, current, [], [], [], [], regressions), 1

    current_set = set(current_keys)
    debt = [repairable[key] for key in base_keys if key in current_set]
    improvements = [repairable[key] for key in base_keys if key not in current_set]
    evidence_active = [item for key, item in evidence_lost.items() if key in current_set]
    evidence_inactive = [item for key, item in evidence_lost.items() if key not in current_set]
    if evidence_active and debt:
        cause = "declared evidence loss plus repairable debt only"
    elif evidence_active:
        cause = "declared evidence loss only"
    elif debt:
        cause = "repairable debt only"
    else:
        cause = "no classified failures"
    return _decision(
        "PASS",
        cause,
        base,
        current,
        debt,
        improvements,
        evidence_active,
        evidence_inactive,
        [],
    ), 0


def _decision(
    status: str,
    first_cause: str,
    base: dict[str, Any],
    current: dict[str, Any],
    repairable_debt: list[dict[str, Any]],
    repairable_improvements: list[dict[str, Any]],
    evidence_loss_active: list[dict[str, Any]],
    evidence_loss_inactive: list[dict[str, Any]],
    regressions: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema": DECISION_SCHEMA,
        "status": status,
        "first_cause": first_cause,
        "comparison_pytest_exit": base.get("pytest_exit"),
        "current_pytest_exit": current.get("pytest_exit"),
        "repairable_debt": repairable_debt,
        "repairable_improvements": repairable_improvements,
        "evidence_loss_active": evidence_loss_active,
        "evidence_loss_inactive": evidence_loss_inactive,
        "owner_decision": "E_UNDECIDED",
        "regressions": regressions,
    }


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(repo), *args], text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )


def validate_refs(repo: Path, manifest: dict[str, Any], base_sha: str) -> None:
    shas = [base_sha] + [item["sha"] for item in manifest["measured_refs"]]
    for sha in shas:
        resolved = _git(repo, "rev-parse", "--verify", f"{sha}^{{commit}}")
        if resolved.returncode != 0:
            raise RuntimeError(f"unresolvable commit SHA: {sha}")
    head = _git(repo, "rev-parse", "HEAD")
    if head.returncode != 0:
        raise RuntimeError("cannot resolve current HEAD")
    for item in manifest["measured_refs"]:
        ancestry = _git(repo, "merge-base", "--is-ancestor", item["sha"], head.stdout.strip())
        if ancestry.returncode != 0:
            raise RuntimeError(f"measured SHA is not an ancestor of HEAD: {item['sha']}")


def run_pytest(repo: Path, nodeids: list[str], timeout_seconds: int) -> dict[str, Any]:
    handle, report_name = tempfile.mkstemp(prefix="pytest-inventory-", suffix=".json")
    os.close(handle)
    report_path = Path(report_name)
    report_path.unlink(missing_ok=True)
    env = os.environ.copy()
    plugin_dir = str(Path(__file__).resolve().parent)
    env["PYTHONPATH"] = plugin_dir + os.pathsep + env.get("PYTHONPATH", "")
    env["PYTEST_TRIAGE_REPORT"] = str(report_path)
    command = [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        "-p",
        "pytest_scientific_triage_guard",
        *nodeids,
    ]
    print("PYTEST_TRIAGE_COMMAND=" + " ".join(command), flush=True)
    try:
        completed = subprocess.run(command, cwd=repo, env=env, timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        report_path.unlink(missing_ok=True)
        return {"timed_out": True, "pytest_exit": 124, "collected": [], "failures": [], "collection_errors": []}
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"pytest inventory absent or corrupt: {exc}") from exc
    finally:
        report_path.unlink(missing_ok=True)
    report["process_exit"] = completed.returncode
    report["timed_out"] = False
    return report


def write_decision(path: Path, decision: dict[str, Any], exit_code: int) -> int:
    decision = dict(decision)
    decision["exit_code"] = exit_code
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(decision, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)
    print(json.dumps(decision, indent=2, sort_keys=True), flush=True)
    return exit_code


def _early_result(argv: list[str]) -> Path | None:
    if "--result" not in argv:
        return None
    index = argv.index("--result")
    return Path(argv[index + 1]) if index + 1 < len(argv) else None


def main(argv: list[str] | None = None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    early = _early_result(arguments)
    if early is not None:
        try:
            invalidate_result(early)
        except RuntimeError as exc:
            print(f"FAIL: {exc}", file=sys.stderr)
            return 2
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--result", required=True, type=Path)
    parser.add_argument("--comparison-base", required=True)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--timeout-seconds", type=int, default=1200)
    args = parser.parse_args(arguments)
    try:
        manifest = load_manifest(args.manifest)
        repo = args.repo.resolve()
        validate_refs(repo, manifest, args.comparison_base)
        with tempfile.TemporaryDirectory(prefix="pytest-triage-base-") as worktree_name:
            worktree = Path(worktree_name)
            added = _git(repo, "worktree", "add", "--detach", str(worktree), args.comparison_base)
            if added.returncode != 0:
                raise RuntimeError(f"comparison worktree failed: {added.stderr.strip()}")
            try:
                nodeids = [
                    item["nodeid"]
                    for item in _class_items(manifest, CLASS_C)
                ]
                base = run_pytest(worktree, nodeids, args.timeout_seconds)
            finally:
                removed = _git(repo, "worktree", "remove", "--force", str(worktree))
                if removed.returncode != 0:
                    raise RuntimeError(f"comparison worktree cleanup failed: {worktree}")
        current = run_pytest(repo, [], args.timeout_seconds)
        decision, code = evaluate(manifest, base, current)
        return write_decision(args.result, decision, code)
    except Exception as exc:
        decision = _decision(
            "FAIL",
            str(exc),
            {},
            {},
            [],
            [],
            [],
            [],
            [{"kind": "guard error", "detail": str(exc)}],
        )
        return write_decision(args.result, decision, 2)


if __name__ == "__main__":
    raise SystemExit(main())
