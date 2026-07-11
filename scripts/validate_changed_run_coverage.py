"""Require provenance manifests for newly changed computational text artifacts."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_DIR = ROOT / "run-manifests"
COMPUTATIONAL_TEXT = re.compile(
    r"^scripts/.*(?:transcript|output).*\.txt$", re.IGNORECASE
)


def git_changes(root: Path, base: str) -> list[tuple[str, str]]:
    result = subprocess.run(
        ["git", "diff", "--name-status", f"{base}...HEAD"],
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or "git diff failed")
    changes: list[tuple[str, str]] = []
    for line in result.stdout.splitlines():
        fields = line.split("\t")
        if len(fields) < 2:
            continue
        status = fields[0]
        # Rename/copy records contain old and new paths; only the new path can
        # be live evidence in the resulting tree.
        path = fields[-1].replace("\\", "/")
        changes.append((status, path))
    return changes


def indexed_outputs(manifest_dir: Path) -> set[str]:
    outputs: set[str] = set()
    if not manifest_dir.is_dir():
        return outputs
    for path in sorted(manifest_dir.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            # The complete manifest validator reports the structural error.
            continue
        if not isinstance(data, dict):
            continue
        artifacts = data.get("outputs")
        if not isinstance(artifacts, list):
            continue
        for artifact in artifacts:
            if isinstance(artifact, dict) and isinstance(artifact.get("path"), str):
                outputs.add(artifact["path"].replace("\\", "/"))
    return outputs


def validate_changed_coverage(
    changes: Iterable[tuple[str, str]], manifest_dir: Path = MANIFEST_DIR
) -> list[str]:
    covered = indexed_outputs(manifest_dir)
    errors: list[str] = []
    for status, path in changes:
        if status.startswith("D") or not COMPUTATIONAL_TEXT.fullmatch(path):
            continue
        if path not in covered:
            errors.append(
                f"{path}: changed computational artifact is not listed in any "
                "run-manifest output"
            )
    return sorted(set(errors))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, help="Git base commit for the change set")
    args = parser.parse_args(argv)
    try:
        changes = git_changes(ROOT, args.base)
    except RuntimeError as exc:
        print(f"changed-run coverage failed: {exc}")
        return 1
    errors = validate_changed_coverage(changes)
    if errors:
        print(f"changed-run coverage: {len(errors)} problem(s)")
        for error in errors:
            print(f"  - {error}")
        return 1
    checked = sum(
        1
        for status, path in changes
        if not status.startswith("D") and COMPUTATIONAL_TEXT.fullmatch(path)
    )
    print(f"changed-run coverage OK: {checked} computational artifact(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
