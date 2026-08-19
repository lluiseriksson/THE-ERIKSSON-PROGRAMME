#!/usr/bin/env python3
"""Fail-closed mechanical promotion of Step 8b.23 Unit F."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PREVIEW = runpy.run_path(str(ROOT / "tmp" / "audit_step8b23_promotion_preview.py"))
AE_LIST = ROOT / "tmp" / "STEP8B23-UNIT-E-PREFIX-PATHS.txt"
F_LIST = ROOT / "tmp" / "STEP8B23-UNIT-F-EXTENSION-PATHS.txt"
EXPECTED_AE_SEALED_DIGEST = (
    "07C83157A79B64A12F5135423F86F76252E092CD185D0D58FDF61694A34C1978"
)
EXPECTED_F_PROMOTED_DIGEST = (
    "AEC2A745A059DBFA7F24F8F52233156F9569ECF8AF35329292B0F3BDDCA7C619"
)


def listed(path: Path) -> list[Path]:
    return [
        ROOT / raw.strip()
        for raw in path.read_text(encoding="utf-8-sig").splitlines()
        if raw.strip() and not raw.lstrip().startswith("#")
    ]


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


def sealed_content(draft: Path) -> bytes:
    promoted = PREVIEW["transform"](draft)[0].decode("utf-8")
    marker: str = PREVIEW["PRE_VALIDATION"]
    if promoted.count(marker) != 1:
        raise SystemExit(f"PRE_MARKER_COUNT={draft.name}/{promoted.count(marker)}")
    return promoted.replace(marker, "", 1).encode("utf-8")


def ae_prerequisites() -> list[tuple[Path, bytes]]:
    result: list[tuple[Path, bytes]] = []
    rows: list[str] = []
    for draft in listed(AE_LIST):
        target: Path = PREVIEW["target_of"](draft)
        content = sealed_content(draft)
        result.append((target, content))
        rows.append(
            f"{hashlib.sha256(content).hexdigest()}  {target.relative_to(ROOT).as_posix()}\n"
        )
    digest = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    if len(result) != 36 or digest != EXPECTED_AE_SEALED_DIGEST:
        raise SystemExit(f"AE_PREREQUISITE_PLAN_MISMATCH={len(result)}/{digest}")
    return result


def f_plan() -> list[tuple[Path, bytes]]:
    result: list[tuple[Path, bytes]] = []
    rows: list[str] = []
    for draft in listed(F_LIST):
        target: Path = PREVIEW["target_of"](draft)
        if target.exists():
            raise SystemExit(f"UNIT_F_TARGET_ALREADY_EXISTS={target.relative_to(ROOT)}")
        content = PREVIEW["transform"](draft)[0]
        result.append((target, content))
        rows.append(
            f"{hashlib.sha256(content).hexdigest()}  {target.relative_to(ROOT).as_posix()}\n"
        )
    digest = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    if len(result) != 8 or digest != EXPECTED_F_PROMOTED_DIGEST:
        raise SystemExit(f"UNIT_F_PLAN_MISMATCH={len(result)}/{digest}")
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

    prerequisites = ae_prerequisites()
    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    for target, expected in prerequisites:
        if not target.is_file():
            raise SystemExit(f"SEALED_AE_PREREQUISITE_MISSING={target.relative_to(ROOT)}")
        if target.read_bytes() != expected:
            raise SystemExit(f"SEALED_AE_PREREQUISITE_DRIFT={target.relative_to(ROOT)}")
        if target.name.endswith("Audit.lean"):
            module = target.with_suffix("").relative_to(ROOT).as_posix().replace("/", ".")
            if f"import {module}" not in core:
                raise SystemExit(f"SEALED_AE_AUDIT_NOT_IN_CORE={module}")
    promotion = f_plan()
    if not args.write:
        print(
            "STEP8B23_F_PROMOTION_DRY_RUN_OK "
            f"head={actual} prerequisites=36 new_files=8 "
            f"manifest={EXPECTED_F_PROMOTED_DIGEST}"
        )
        return 0

    for target, content in promotion:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in promotion:
        if target.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(
        "STEP8B23_F_PROMOTION_WRITE_OK "
        f"base_head={actual} prerequisites=36 new_files=8 "
        f"manifest={EXPECTED_F_PROMOTED_DIGEST}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
