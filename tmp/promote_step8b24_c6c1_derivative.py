#!/usr/bin/env python3
"""Fail-closed mechanical promotion of Step 8b.24 C6c.1 D1--D4d."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
sys.path.insert(0, str(TMP))
PROMOTION = runpy.run_path(str(TMP / "audit_step8b24_promotion_preview.py"))

PREREQUISITE_LIST = TMP / "STEP8B24-ALL-PATHS.txt"
EXPECTED_PREREQUISITE_LIST_SHA256 = (
    "04D159C779790BBC9E7B5CB6BEB98EE1309245B252AD177E7D97C359819EE63B"
)
DERIVATIVE_LISTS: tuple[tuple[Path, str, int], ...] = (
    (
        TMP / "STEP8B24-C6C1-PREFIX-PATHS.txt",
        "C8A9F71F0723F914E0380A9A8038AB72510FCE602C1291995FCA4D5EF4A2E938",
        8,
    ),
    (
        TMP / "STEP8B24-C6C1-D4-PATHS.txt",
        "D00253F5ADC61A56214DEDEA1D84115ECFD3CFF5B628AF7472084454B0D7F36A",
        6,
    ),
)
EXPECTED_PROMOTION_MANIFEST_SHA256 = (
    "7D82089113F6ADB6058C686ABA7B994B0C6B953C953BAE0555B07A6DE2792581"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


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


def rows(path_list: Path, expected_digest: str, expected_count: int) -> list[str]:
    measured = sha256(path_list.read_bytes())
    if measured != expected_digest:
        raise SystemExit(f"PATH_LIST_DRIFT={path_list.name}/{measured}")
    result = [
        raw.strip()
        for raw in path_list.read_text(encoding="utf-8-sig").splitlines()
        if raw.strip() and not raw.lstrip().startswith("#")
    ]
    if len(result) != expected_count:
        raise SystemExit(f"PATH_LIST_COUNT={path_list.name}/{len(result)}")
    return result


def target_of_draft_row(raw: str) -> Path:
    if not raw.startswith("tmp/") or not raw.endswith(".draft.lean"):
        raise SystemExit(f"BAD_DRAFT_PATH={raw}")
    stem = raw.removeprefix("tmp/").removesuffix(".draft.lean")
    return Path("YangMills") / "RG" / f"{stem}.lean"


def require_sealed_prerequisites() -> None:
    raw_rows = rows(PREREQUISITE_LIST, EXPECTED_PREREQUISITE_LIST_SHA256, 78)
    targets = [target_of_draft_row(raw) for raw in raw_rows]
    if len(targets) != 78 or len(targets) != len(set(targets)):
        raise SystemExit(f"PREREQUISITE_SCOPE_MISMATCH={len(targets)}")

    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    for relative in targets:
        target = ROOT / relative
        if not target.is_file():
            raise SystemExit(f"PREREQUISITE_MISSING={relative.as_posix()}")
        text = target.read_text(encoding="utf-8")
        if "PRE-VALIDATION:" in text:
            raise SystemExit(f"PREREQUISITE_NOT_SEALED={relative.as_posix()}")
        if relative.name.endswith("Audit.lean"):
            module = relative.with_suffix("").as_posix().replace("/", ".")
            if f"import {module}" not in core:
                raise SystemExit(f"PREREQUISITE_AUDIT_NOT_IN_CORE={module}")


def promotion_plan() -> list[tuple[Path, bytes]]:
    require_sealed_prerequisites()
    raw_rows: list[str] = []
    for path_list, digest, count in DERIVATIVE_LISTS:
        raw_rows.extend(rows(path_list, digest, count))
    if len(raw_rows) != 14 or len(raw_rows) != len(set(raw_rows)):
        raise SystemExit(f"DERIVATIVE_SCOPE_MISMATCH={len(raw_rows)}")

    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    result: list[tuple[Path, bytes]] = []
    manifest_rows: list[str] = []
    for raw in raw_rows:
        source = ROOT / raw
        relative = target_of_draft_row(raw)
        target = ROOT / relative
        if not source.is_file():
            raise SystemExit(f"DERIVATIVE_DRAFT_MISSING={raw}")
        if target.exists():
            raise SystemExit(f"DERIVATIVE_TARGET_ALREADY_EXISTS={relative.as_posix()}")
        content = PROMOTION["transform"](source)[0]
        if content.decode("utf-8").count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"DERIVATIVE_PRE_MARKER_COUNT={relative.as_posix()}")
        if relative.name.endswith("Audit.lean"):
            module = relative.with_suffix("").as_posix().replace("/", ".")
            if f"import {module}" in core:
                raise SystemExit(f"DERIVATIVE_AUDIT_PREMATURELY_IN_CORE={module}")
        result.append((target, content))
        manifest_rows.append(
            f"{hashlib.sha256(content).hexdigest()}  {relative.as_posix()}\n"
        )
    digest = sha256("".join(manifest_rows).encode())
    if digest != EXPECTED_PROMOTION_MANIFEST_SHA256:
        raise SystemExit(f"DERIVATIVE_PROMOTION_MANIFEST_DRIFT={digest}")
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

    promotion = promotion_plan()
    if not args.write:
        print(
            "STEP8B24_C6C1_DERIVATIVE_PROMOTION_DRY_RUN_OK "
            f"head={actual} prerequisites=78 new_files={len(promotion)} "
            f"manifest={EXPECTED_PROMOTION_MANIFEST_SHA256}"
        )
        return 0

    for target, content in promotion:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in promotion:
        if target.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(
        "STEP8B24_C6C1_DERIVATIVE_PROMOTION_WRITE_OK "
        f"base_head={actual} prerequisites=78 new_files={len(promotion)} "
        f"manifest={EXPECTED_PROMOTION_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
