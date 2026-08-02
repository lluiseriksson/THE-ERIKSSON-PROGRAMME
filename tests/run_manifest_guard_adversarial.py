"""Executable adversarial scenarios for the run-manifest debt guard.

This file deliberately uses explicit exceptions instead of ``assert`` so the
same decisions execute under both normal Python and ``python -O``.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import shutil
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VALIDATOR_PATH = ROOT / "scripts" / "validate_run_manifests.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def load_validator():
    spec = importlib.util.spec_from_file_location("validate_run_manifests", VALIDATOR_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load validator from {VALIDATOR_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valid_manifest(root: Path, run_id: str) -> dict:
    script = root / "scripts" / "run.py"
    output = root / "outputs" / f"{run_id}.txt"
    script.parent.mkdir(parents=True, exist_ok=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    script.write_text("print('run')\n", encoding="utf-8")
    output.write_text("evidence\n", encoding="utf-8")
    return {
        "schema_version": 1,
        "run_id": run_id,
        "claim_scope": "official fixture publication title",
        "status": "current",
        "started_utc": "2026-08-02T12:00:00Z",
        "finished_utc": "2026-08-02T12:00:01Z",
        "command": ["python", "scripts/run.py"],
        "working_directory": ".",
        "script": {"path": "scripts/run.py", "sha256": digest(script)},
        "environment": {"python": "3.12", "libraries": {}},
        "inputs": [],
        "outputs": [{"path": f"outputs/{run_id}.txt", "sha256": digest(output)}],
        "supersedes": [],
        "superseded_by": None,
        "quarantine_reason": None,
    }


def write_manifest(root: Path, data: dict) -> Path:
    directory = root / "run-manifests"
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{data['run_id']}.json"
    path.write_text(json.dumps(data), encoding="utf-8")
    return path


def report(
    validator, root: Path, baseline: Path, comparison_root: Path | None = None
) -> dict:
    return validator.evaluate_debt_guard(
        root=root,
        manifest_dir=root / "run-manifests",
        baseline_path=baseline,
        require_nonempty=True,
        comparison_root=comparison_root,
    )


def require_pass(result: dict, scenario: str) -> None:
    require(not result["guard_errors"], f"{scenario}: expected PASS, got {result['guard_errors']}")


def require_fail(result: dict, needle: str, scenario: str) -> None:
    joined = "\n".join(result["guard_errors"])
    require(bool(result["guard_errors"]), f"{scenario}: expected failure")
    require(needle in joined, f"{scenario}: missing cause {needle!r} in {joined!r}")


def main() -> int:
    validator = load_validator()
    outcomes: dict[str, str] = {}
    with tempfile.TemporaryDirectory(prefix="run-manifest-guard-") as temporary:
        root = Path(temporary) / "current"
        root.mkdir()
        legacy = valid_manifest(root, "legacy-run")
        legacy["environment"] = None
        legacy_path = write_manifest(root, legacy)
        baseline_data = validator.build_debt_baseline(
            root=root,
            manifest_dir=root / "run-manifests",
            base_sha="0" * 40,
        )
        baseline = root / "debt-baseline.json"
        baseline.write_text(
            json.dumps(baseline_data, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        comparison_root = Path(temporary) / "comparison"
        shutil.copytree(root, comparison_root)

        require_pass(
            report(validator, root, baseline, comparison_root), "exact baseline"
        )
        outcomes["exact_baseline"] = "PASS"

        malformed = root / "run-manifests" / "new-malformed.json"
        malformed.write_text("{}\n", encoding="utf-8")
        require_fail(
            report(validator, root, baseline, comparison_root),
            "new manifest is invalid",
            "new malformed manifest",
        )
        outcomes["new_malformed_manifest"] = "REJECTED"
        malformed.unlink()

        worsened = dict(legacy)
        worsened["command"] = None
        legacy_path.write_text(json.dumps(worsened), encoding="utf-8")
        require_fail(
            report(validator, root, baseline, comparison_root),
            "debt increased for command",
            "existing manifest worsened",
        )
        outcomes["existing_debt_increase"] = "REJECTED"
        legacy_path.write_text(json.dumps(legacy), encoding="utf-8")

        repaired = dict(legacy)
        repaired["environment"] = {"python": "3.12", "libraries": {}}
        legacy_path.write_text(json.dumps(repaired), encoding="utf-8")
        require_pass(
            report(validator, root, baseline, comparison_root),
            "real debt reduction",
        )
        outcomes["debt_reduction"] = "PASS"
        legacy_path.write_text(json.dumps(legacy), encoding="utf-8")

        comparison_legacy = comparison_root / "run-manifests" / legacy_path.name
        comparison_repaired = dict(legacy)
        comparison_repaired["environment"] = {
            "python": "3.12",
            "libraries": {},
        }
        comparison_legacy.write_text(
            json.dumps(comparison_repaired), encoding="utf-8"
        )
        require_fail(
            report(validator, root, baseline, comparison_root),
            "debt increased for environment",
            "reintroduced repaired debt",
        )
        outcomes["reintroduced_repaired_debt"] = "REJECTED"
        comparison_legacy.write_text(json.dumps(legacy), encoding="utf-8")

        original = legacy_path.read_text(encoding="utf-8")
        legacy_path.unlink()
        require_fail(
            report(validator, root, baseline, comparison_root),
            "protected publication was deleted",
            "publication deletion",
        )
        outcomes["publication_deletion"] = "REJECTED"
        legacy_path.write_text(original, encoding="utf-8")

        retitled = dict(legacy)
        retitled["claim_scope"] = "incorrect replacement title"
        legacy_path.write_text(json.dumps(retitled), encoding="utf-8")
        require_fail(
            report(validator, root, baseline, comparison_root),
            "official scope/title changed",
            "official title replacement",
        )
        outcomes["official_title_replacement"] = "REJECTED"
        legacy_path.write_text(json.dumps(legacy), encoding="utf-8")

        malformed.write_text("{}\n", encoding="utf-8")
        result_file = root / "guard-result.json"
        result_file.write_text(
            json.dumps({"status": "PASS", "stale_marker": True}), encoding="utf-8"
        )
        exit_code = validator.main(
            [
                "--root",
                str(root),
                "--require-nonempty",
                "--baseline",
                str(baseline),
                "--comparison-root",
                str(comparison_root),
                "--result-file",
                str(result_file),
            ]
        )
        result_data = json.loads(result_file.read_text(encoding="utf-8"))
        require(exit_code == 1, f"stale PASS scenario: expected exit 1, got {exit_code}")
        require(result_data.get("status") == "FAIL", "stale PASS was not replaced by FAIL")
        require(result_data.get("exit_code") == 1, "result did not record exit code 1")
        require(bool(result_data.get("first_cause")), "result did not record first cause")
        require("stale_marker" not in result_data, "stale PASS payload was not truncated")
        outcomes["stale_pass_on_failure"] = "INVALIDATED"

    print(json.dumps(outcomes, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
