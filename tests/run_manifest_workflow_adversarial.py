"""Exercise the workflow's pre-validator stale-decision failure boundary."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CI_GUARD_PATH = ROOT / "scripts" / "run_manifest_guard_ci.sh"
WORKFLOW_PATH = ROOT / ".github" / "workflows" / "control-plane.yml"


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


def main() -> int:
    workflow = WORKFLOW_PATH.read_text(encoding="utf-8")
    guard_job = workflow.split("  run-manifest-structure-debt-delta:", 1)[1].split(
        "\n  test:", 1
    )[0]
    invalidation = guard_job.index(
        "- name: Invalidate any pre-existing run-manifest decision record"
    )
    checkout = guard_job.index("- uses: actions/checkout@v4")
    materialization = guard_job.index("bash scripts/run_manifest_guard_ci.sh")
    require(invalidation < checkout < materialization, "decision invalidation is not first")
    require("if: always()" in guard_job, "decision artifact is not attempted on failure")
    require(
        "if-no-files-found: error" in guard_job,
        "an absent decision record would not fail publication",
    )

    with tempfile.TemporaryDirectory(prefix="run-manifest-workflow-guard-") as raw:
        temporary = Path(raw)
        result = temporary / "run-manifest-guard-result.json"
        result.write_text(
            json.dumps({"status": "PASS", "exit_code": 0, "stale_marker": True}),
            encoding="utf-8",
        )
        child = subprocess.run(
            [
                bash_executable(),
                CI_GUARD_PATH.as_posix(),
                result.as_posix(),
                (temporary / "comparison").as_posix(),
                "refs/heads/__missing_run_manifest_guard_base__",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        require(child.returncode != 0, "pre-validator child unexpectedly passed")
        require(not result.exists(), "stale PASS survived the pre-validator failure")
        print(
            json.dumps(
                {
                    "pre_validator_exit_code": child.returncode,
                    "decision_record_state": "ABSENT",
                    "stale_pass_publishable": False,
                    "first_stderr_line": (
                        child.stderr.splitlines()[0]
                        if child.stderr.splitlines()
                        else None
                    ),
                },
                sort_keys=True,
            )
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
