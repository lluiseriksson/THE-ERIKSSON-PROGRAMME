"""Execute every workflow-wrapper exit path against a pre-seeded PASS record."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CI_GUARD_PATH = ROOT / "scripts" / "run_manifest_guard_ci.sh"
VALIDATOR_PATH = ROOT / "scripts" / "validate_run_manifests.py"
CANONICAL_RESULT_NAME = "run-manifest-guard-result.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def bash_executable() -> str:
    if os.name == "nt":
        git_bash = Path("C:/Program Files/Git/bin/bash.exe")
        if git_bash.is_file():
            return str(git_bash)
    executable = shutil.which("bash")
    if executable is None:
        raise RuntimeError("bash is required to exercise the workflow guard")
    return executable


def load_validator():
    spec = importlib.util.spec_from_file_location(
        "workflow_fixture_validate_run_manifests", VALIDATOR_PATH
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load validator from {VALIDATOR_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_git(repository: Path, *arguments: str) -> None:
    child = subprocess.run(
        ["git", *arguments],
        cwd=repository,
        capture_output=True,
        text=True,
        check=False,
    )
    require(
        child.returncode == 0,
        f"git {' '.join(arguments)} failed: {child.stderr or child.stdout}",
    )


def create_repository(parent: Path) -> Path:
    repository = parent / "repository"
    (repository / "scripts").mkdir(parents=True)
    (repository / "outputs").mkdir()
    (repository / "run-manifests").mkdir()
    (repository / ".github").mkdir()
    shutil.copy2(VALIDATOR_PATH, repository / "scripts" / VALIDATOR_PATH.name)

    script = repository / "scripts" / "run.py"
    output = repository / "outputs" / "fixture.txt"
    script.write_text("print('fixture')\n", encoding="utf-8")
    output.write_text("fixture evidence\n", encoding="utf-8")
    manifest = {
        "schema_version": 1,
        "run_id": "workflow-fixture",
        "claim_scope": "workflow fixture publication",
        "status": "current",
        "started_utc": "2026-08-02T12:00:00Z",
        "finished_utc": "2026-08-02T12:00:01Z",
        "command": ["python", "scripts/run.py"],
        "working_directory": ".",
        "script": {"path": "scripts/run.py", "sha256": digest(script)},
        "environment": {"python": "3.12", "libraries": {}},
        "inputs": [],
        "outputs": [{"path": "outputs/fixture.txt", "sha256": digest(output)}],
        "supersedes": [],
        "superseded_by": None,
        "quarantine_reason": None,
    }
    (repository / "run-manifests" / "workflow-fixture.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    validator = load_validator()
    baseline = validator.build_debt_baseline(
        root=repository,
        manifest_dir=repository / "run-manifests",
        base_sha="0" * 40,
    )
    (repository / ".github" / "run-manifest-debt-baseline.json").write_text(
        json.dumps(baseline, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    run_git(repository, "init", "-q")
    run_git(repository, "config", "user.name", "run-manifest-guard-fixture")
    run_git(repository, "config", "user.email", "fixture@example.invalid")
    run_git(repository, "add", "--", ".")
    run_git(repository, "commit", "-q", "-m", "fixture base")
    return repository


def seed_stale_pass(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"status": "PASS", "exit_code": 0, "stale_marker": True})
        + "\n",
        encoding="utf-8",
    )


def decision_state(path: Path) -> tuple[str, dict | None]:
    if not path.exists():
        return "ABSENT", None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return f"PRESENT/UNREADABLE:{type(exc).__name__}", None
    if payload.get("status") != "PASS":
        return "FAIL/no-PASS", payload
    if payload.get("stale_marker"):
        return "PRESENT/PASS", payload
    if payload.get("exit_code") == 0 and payload.get("first_cause") is None:
        return "PASS/new-valid", payload
    return "PRESENT/PASS", payload


def execute(
    *,
    repository: Path,
    result_file: Path,
    arguments: list[str],
    optimized: bool,
    caller_preclean: bool = False,
) -> dict:
    seed_stale_pass(result_file)
    environment = os.environ.copy()
    if optimized:
        environment["PYTHONOPTIMIZE"] = "1"
    else:
        environment.pop("PYTHONOPTIMIZE", None)

    if caller_preclean:
        workspace = result_file.parent
        require(
            result_file == workspace / CANONICAL_RESULT_NAME,
            "missing-$1 fixture is not using the caller's canonical result path",
        )
        environment["GITHUB_WORKSPACE"] = workspace.as_posix()
        environment["RUN_MANIFEST_GUARD_SCRIPT"] = CI_GUARD_PATH.as_posix()
        command = [
            bash_executable(),
            "-c",
            'rm -f -- "$GITHUB_WORKSPACE/run-manifest-guard-result.json"\n'
            'test ! -e "$GITHUB_WORKSPACE/run-manifest-guard-result.json"\n'
            'bash "$RUN_MANIFEST_GUARD_SCRIPT"',
        ]
    else:
        command = [bash_executable(), CI_GUARD_PATH.as_posix(), *arguments]

    child = subprocess.run(
        command,
        cwd=repository,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    state, payload = decision_state(result_file)
    return {
        "exit_code": child.returncode,
        "decision_state": state,
        "recorded_exit_code": payload.get("exit_code") if payload else None,
        "first_cause": payload.get("first_cause") if payload else None,
        "stale_marker_survived": bool(payload and payload.get("stale_marker")),
        "first_stderr_line": (
            child.stderr.splitlines()[0] if child.stderr.splitlines() else None
        ),
    }


def require_outcome(
    record: dict,
    *,
    scenario: str,
    exit_code: int,
    decision_state_name: str,
) -> None:
    require(
        record["exit_code"] == exit_code,
        f"{scenario}: expected exit {exit_code}, got {record['exit_code']}",
    )
    require(
        record["decision_state"] == decision_state_name,
        f"{scenario}: expected {decision_state_name}, got {record['decision_state']}",
    )
    require(
        not record["stale_marker_survived"],
        f"{scenario}: stale PASS marker survived",
    )


def exercise_mode(parent: Path, *, optimized: bool) -> dict[str, dict]:
    repository = create_repository(parent)
    mode = "optimized" if optimized else "normal"
    records: dict[str, dict] = {}

    workspace_a = parent / "a-workspace"
    result_a = workspace_a / CANONICAL_RESULT_NAME
    records["a_missing_result_file"] = execute(
        repository=repository,
        result_file=result_a,
        arguments=[],
        optimized=optimized,
        caller_preclean=True,
    )
    require_outcome(
        records["a_missing_result_file"],
        scenario=f"{mode}/a",
        exit_code=1,
        decision_state_name="ABSENT",
    )

    result_b = parent / "b-workspace" / CANONICAL_RESULT_NAME
    records["b_missing_comparison_root"] = execute(
        repository=repository,
        result_file=result_b,
        arguments=[result_b.as_posix()],
        optimized=optimized,
    )
    require_outcome(
        records["b_missing_comparison_root"],
        scenario=f"{mode}/b",
        exit_code=1,
        decision_state_name="ABSENT",
    )

    result_c = parent / "c-workspace" / CANONICAL_RESULT_NAME
    records["c_missing_change_base"] = execute(
        repository=repository,
        result_file=result_c,
        arguments=[result_c.as_posix(), (parent / "c-comparison").as_posix()],
        optimized=optimized,
    )
    require_outcome(
        records["c_missing_change_base"],
        scenario=f"{mode}/c",
        exit_code=1,
        decision_state_name="ABSENT",
    )

    result_d = parent / "d-workspace" / CANONICAL_RESULT_NAME
    comparison_d = parent / "d-comparison"
    records["d_materialization_failure"] = execute(
        repository=repository,
        result_file=result_d,
        arguments=[
            result_d.as_posix(),
            comparison_d.as_posix(),
            "refs/heads/__missing_guard_base__",
        ],
        optimized=optimized,
    )
    require_outcome(
        records["d_materialization_failure"],
        scenario=f"{mode}/d",
        exit_code=128,
        decision_state_name="ABSENT",
    )

    baseline_path = repository / ".github" / "run-manifest-debt-baseline.json"
    valid_baseline = baseline_path.read_text(encoding="utf-8")
    baseline_path.write_text("{invalid baseline\n", encoding="utf-8")
    result_e = parent / "e-workspace" / CANONICAL_RESULT_NAME
    comparison_e = parent / "e-comparison"
    records["e_python_failure"] = execute(
        repository=repository,
        result_file=result_e,
        arguments=[result_e.as_posix(), comparison_e.as_posix(), "HEAD"],
        optimized=optimized,
    )
    require_outcome(
        records["e_python_failure"],
        scenario=f"{mode}/e",
        exit_code=2,
        decision_state_name="FAIL/no-PASS",
    )
    require(
        records["e_python_failure"]["recorded_exit_code"] == 2,
        f"{mode}/e: FAIL record did not preserve exit 2",
    )
    require(
        bool(records["e_python_failure"]["first_cause"]),
        f"{mode}/e: FAIL record has no first cause",
    )
    require(not comparison_e.exists(), f"{mode}/e: comparison worktree survived")
    baseline_path.write_text(valid_baseline, encoding="utf-8")

    result_f = parent / "f-workspace" / CANONICAL_RESULT_NAME
    comparison_f = parent / "f-comparison"
    records["f_success"] = execute(
        repository=repository,
        result_file=result_f,
        arguments=[result_f.as_posix(), comparison_f.as_posix(), "HEAD"],
        optimized=optimized,
    )
    require_outcome(
        records["f_success"],
        scenario=f"{mode}/f",
        exit_code=0,
        decision_state_name="PASS/new-valid",
    )
    require(
        records["f_success"]["recorded_exit_code"] == 0,
        f"{mode}/f: PASS record did not preserve exit 0",
    )
    require(not comparison_f.exists(), f"{mode}/f: comparison worktree survived")
    return records


def main() -> int:
    outcomes: dict[str, dict[str, dict]] = {}
    with tempfile.TemporaryDirectory(prefix="run-manifest-workflow-normal-") as raw:
        outcomes["normal"] = exercise_mode(Path(raw), optimized=False)
    with tempfile.TemporaryDirectory(prefix="run-manifest-workflow-optimized-") as raw:
        outcomes["optimized"] = exercise_mode(Path(raw), optimized=True)
    print(json.dumps(outcomes, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
