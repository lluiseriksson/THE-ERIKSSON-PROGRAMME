#!/usr/bin/env python3
"""Fail-closed mechanical promotion of the staged Step 8b.24 extension."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tmp"))
PREVIEW = runpy.run_path(
    str(ROOT / "tmp" / "audit_step8b24_extension_promotion_preview.py")
)
P24 = PREVIEW["P24"]
SCHEDULE = PREVIEW["SCHEDULE"]
OWNERSHIP = PREVIEW["OWNERSHIP"]
EXPECTED_PREREQUISITE_DIGEST = (
    "242097332A9545564915A67424A7E34984D477B5B6FA2E918619C27BFC463457"
)
EXPECTED_EXTENSION_DIGEST = (
    "CD6723D3B6EC70B9C004998BB25721E98A474F303F45AB09465DE6E3EE714C6B"
)


def git(*args: str) -> str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit("GIT_FAIL " + " ".join(args) + "\n" + child.stderr)
    return child.stdout.strip()


def prerequisite_plan() -> list[tuple[Path, bytes]]:
    names = [
        name for _, group in SCHEDULE["STEP8B23_SCHEDULE"] for name in group
    ]
    result: list[tuple[Path, bytes]] = []
    rows: list[str] = []
    for name in names:
        for audit in (False, True):
            source = PREVIEW["draft"](name, audit=audit)
            target = PREVIEW["target"](name, audit=audit)
            content = PREVIEW["sealed_step8b23_content"](source)
            result.append((target, content))
            rows.append(
                f"{hashlib.sha256(content).hexdigest()}  "
                f"{target.relative_to(ROOT).as_posix()}\n"
            )
    digest = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    if len(result) != 44 or digest != EXPECTED_PREREQUISITE_DIGEST:
        raise SystemExit(f"PREREQUISITE_PLAN_MISMATCH={len(result)}/{digest}")
    return result


def extension_plan() -> list[tuple[Path, bytes]]:
    names = [name for _, name in SCHEDULE["STEP8B24_SCHEDULE"]]
    result: list[tuple[Path, bytes]] = []
    rows: list[str] = []
    for name in names:
        for audit in (False, True):
            source = PREVIEW["draft"](name, audit=audit)
            target = PREVIEW["target"](name, audit=audit)
            if target.exists():
                raise SystemExit(f"EXTENSION_TARGET_ALREADY_EXISTS={target.relative_to(ROOT)}")
            content = P24["transform"](source)[0]
            result.append((target, content))
            rows.append(
                f"{hashlib.sha256(content).hexdigest()}  "
                f"{target.relative_to(ROOT).as_posix()}\n"
            )
    old_owner: Path = OWNERSHIP["OLD"]
    old_content: bytes = PREVIEW["proposed_old_owner"]()
    result.append((old_owner, old_content))
    rows.append(
        f"{hashlib.sha256(old_content).hexdigest()}  "
        f"{old_owner.relative_to(ROOT).as_posix()}\n"
    )
    digest = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    if len(result) != 35 or digest != EXPECTED_EXTENSION_DIGEST:
        raise SystemExit(f"EXTENSION_PLAN_MISMATCH={len(result)}/{digest}")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    actual = git("rev-parse", "HEAD")
    if actual != args.expected_head:
        raise SystemExit(f"HEAD_MISMATCH={actual}")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--cached", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("INDEX_NOT_CLEAN")

    prerequisites = prerequisite_plan()
    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    for target, expected in prerequisites:
        if not target.is_file():
            raise SystemExit(f"SEALED_PREREQUISITE_MISSING={target.relative_to(ROOT)}")
        if target.read_bytes() != expected:
            raise SystemExit(f"SEALED_PREREQUISITE_DRIFT={target.relative_to(ROOT)}")
        if target.name.endswith("Audit.lean"):
            module = target.with_suffix("").relative_to(ROOT).as_posix().replace("/", ".")
            if f"import {module}" not in core:
                raise SystemExit(f"SEALED_PREREQUISITE_AUDIT_NOT_IN_CORE={module}")
    extension = extension_plan()
    if not args.write:
        print(
            "STEP8B24_EXTENSION_PROMOTION_DRY_RUN_OK "
            f"head={actual} prerequisites=44 new_files=34 modified_files=1 "
            f"manifest={EXPECTED_EXTENSION_DIGEST}"
        )
        return 0

    for target, content in extension:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in extension:
        if target.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(
        "STEP8B24_EXTENSION_PROMOTION_WRITE_OK "
        f"base_head={actual} prerequisites=44 new_files=34 modified_files=1 "
        f"manifest={EXPECTED_EXTENSION_DIGEST}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
