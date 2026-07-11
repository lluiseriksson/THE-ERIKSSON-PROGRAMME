"""Validate the canonical, stable state of the Lean programme."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
STATE_PATH = ROOT / "project-state.json"
COMMIT = re.compile(r"^[0-9a-f]{7,40}$")
MATHLIB_LAKEFILE = re.compile(
    r'require\s+mathlib\s+from\s+git\s+"[^"]+"\s*@\s*"([0-9a-f]{40})"',
    re.DOTALL,
)


def _safe_file(root: Path, value: Any, field: str, errors: list[str]) -> Path | None:
    if not isinstance(value, str) or not value:
        errors.append(f"{field}: expected a non-empty repository-relative path")
        return None
    candidate = Path(value)
    if candidate.is_absolute():
        errors.append(f"{field}: path must be repository-relative")
        return None
    resolved = (root / candidate).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError:
        errors.append(f"{field}: path escapes the repository")
        return None
    if not resolved.is_file():
        errors.append(f"{field}: evidence file does not exist")
        return None
    return resolved


def _default_ancestor_check(root: Path, commit: str) -> bool:
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )
    return result.returncode == 0


def validate_state(
    data: Any,
    root: Path = ROOT,
    ancestor_check: Callable[[Path, str], bool] = _default_ancestor_check,
) -> list[str]:
    errors: list[str] = []
    if not isinstance(data, dict):
        return ["project-state.json: expected a JSON object"]
    if data.get("schema_version") != 1:
        errors.append("schema_version: expected 1")

    core = data.get("lean_core")
    if not isinstance(core, dict):
        return [*errors, "lean_core: expected an object"]

    checkpoint = core.get("source_checkpoint")
    if not isinstance(checkpoint, str) or not COMMIT.fullmatch(checkpoint):
        errors.append("lean_core.source_checkpoint: expected a 7-40 digit lowercase commit")
    elif not ancestor_check(root, checkpoint):
        errors.append("lean_core.source_checkpoint: commit is missing or not an ancestor")

    toolchain_path = root / "lean-toolchain"
    if not toolchain_path.is_file():
        errors.append("lean-toolchain: file does not exist")
    else:
        actual_toolchain = toolchain_path.read_text(encoding="utf-8").strip()
        if core.get("toolchain") != actual_toolchain:
            errors.append(
                "lean_core.toolchain: does not match lean-toolchain "
                f"({actual_toolchain})"
            )

    mathlib = core.get("mathlib_commit")
    if not isinstance(mathlib, str) or not re.fullmatch(r"[0-9a-f]{40}", mathlib):
        errors.append("lean_core.mathlib_commit: expected a 40 digit lowercase commit")
    else:
        lakefile = root / "lakefile.lean"
        if not lakefile.is_file():
            errors.append("lakefile.lean: file does not exist")
        else:
            match = MATHLIB_LAKEFILE.search(lakefile.read_text(encoding="utf-8"))
            if match is None:
                errors.append("lakefile.lean: pinned Mathlib commit not found")
            elif match.group(1) != mathlib:
                errors.append("lean_core.mathlib_commit: does not match lakefile.lean")

        manifest_path = root / "lake-manifest.json"
        if not manifest_path.is_file():
            errors.append("lake-manifest.json: file does not exist")
        else:
            try:
                manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                errors.append(f"lake-manifest.json: invalid JSON: {exc}")
            else:
                packages = manifest.get("packages", [])
                package = next(
                    (item for item in packages if item.get("name") == "mathlib"), None
                )
                if package is None:
                    errors.append("lake-manifest.json: Mathlib package not found")
                elif package.get("rev") != mathlib or package.get("inputRev") != mathlib:
                    errors.append(
                        "lean_core.mathlib_commit: does not match Mathlib rev/inputRev"
                    )

    build = core.get("latest_recorded_build")
    if not isinstance(build, dict):
        errors.append("lean_core.latest_recorded_build: expected an object")
    else:
        if build.get("status") != "green":
            errors.append("lean_core.latest_recorded_build.status: expected green")
        if not isinstance(build.get("jobs"), int) or build.get("jobs", 0) <= 0:
            errors.append("lean_core.latest_recorded_build.jobs: expected a positive integer")
        _safe_file(
            root,
            build.get("evidence"),
            "lean_core.latest_recorded_build.evidence",
            errors,
        )

    if core.get("allowed_oracle") != [
        "propext",
        "Classical.choice",
        "Quot.sound",
    ]:
        errors.append("lean_core.allowed_oracle: unexpected axiom list or order")

    frontier = data.get("frontier")
    if not isinstance(frontier, dict):
        errors.append("frontier: expected an object")
    else:
        if frontier.get("id") != "hRpoly":
            errors.append("frontier.id: expected hRpoly")
        if frontier.get("status") != "explicit_theorem_hypothesis":
            errors.append("frontier.status: expected explicit_theorem_hypothesis")
        _safe_file(root, frontier.get("evidence"), "frontier.evidence", errors)

    continuum = data.get("continuum")
    if not isinstance(continuum, dict):
        errors.append("continuum: expected an object")
    else:
        if continuum.get("status") != "open":
            errors.append("continuum.status: expected open")
        statement = continuum.get("statement")
        if not isinstance(statement, str) or "No proved" not in statement:
            errors.append("continuum.statement: must state the unproved boundary explicitly")
        _safe_file(root, continuum.get("evidence"), "continuum.evidence", errors)

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, default=STATE_PATH)
    args = parser.parse_args(argv)
    try:
        data = json.loads(args.state.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: {args.state}: {exc}")
        return 1
    errors = validate_state(data, root=ROOT)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        print(f"project state validation failed: {len(errors)} error(s)")
        return 1
    print("project state validation OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
