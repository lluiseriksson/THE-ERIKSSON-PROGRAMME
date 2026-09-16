#!/usr/bin/env python3
"""Fail-closed mechanical promotion of Step 8b.23 Units A--E.

This script is intentionally unusable until Step 8b.22 has been sealed in the
tracked source/audit pair.  ``--write`` is explicit; without it the command is
read-only.  Unit F is never in scope.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PREVIEW = runpy.run_path(str(ROOT / "tmp" / "audit_step8b23_promotion_preview.py"))
AE_LIST = ROOT / "tmp" / "STEP8B23-UNIT-E-PREFIX-PATHS.txt"
EXPECTED_DIGEST = "C1057D840543EB2EF8024B8F90B7D9B785DF7C40D5C15582E3F4E83022F41AD0"
STEP8B22_PAIR = (
    (
        ROOT / "YangMills/RG/BalabanCMP99FlatFiniteGridAliasing.lean",
        "C82E0BB9D43BECE07C5660E7D3170F2289EBC4188969C222ABC6647C9F0EC34A",
    ),
    (
        ROOT / "YangMills/RG/BalabanCMP99FlatFiniteGridAliasingAudit.lean",
        "9B804AFB964B08EED9A2B7910C8013F29BC326FAE5324C55F4130EB6F5A89785",
    ),
)
STEP8B22_RUN = "31991954503"
STEP8B22_SOURCE = "534493728038813f3772f8b3b073237f4da1884e"


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
        raise SystemExit(
            "GIT_FAIL " + " ".join(args) + "\n" + child.stderr
        )
    return child.stdout.strip()


def drafts() -> list[Path]:
    result = [
        ROOT / raw.strip()
        for raw in AE_LIST.read_text(encoding="utf-8-sig").splitlines()
        if raw.strip() and not raw.lstrip().startswith("#")
    ]
    if len(result) != 36 or len(set(result)) != 36:
        raise SystemExit(f"AE_SCOPE_MISMATCH={len(result)}/{len(set(result))}")
    return result


def plan() -> list[tuple[Path, bytes]]:
    result: list[tuple[Path, bytes]] = []
    rows: list[str] = []
    for draft in drafts():
        content, _ = PREVIEW["transform"](draft)
        target: Path = PREVIEW["target_of"](draft)
        if target.exists():
            raise SystemExit(f"PROMOTION_TARGET_ALREADY_EXISTS={target.relative_to(ROOT)}")
        result.append((target, content))
        rows.append(
            f"{hashlib.sha256(content).hexdigest()}  {target.relative_to(ROOT).as_posix()}\n"
        )
    digest = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    if digest != EXPECTED_DIGEST:
        raise SystemExit(f"PROMOTION_DIGEST_MISMATCH={digest}")
    return result


def require_step8b22_sealed() -> None:
    for path, expected_digest in STEP8B22_PAIR:
        measured = hashlib.sha256(path.read_bytes()).hexdigest().upper()
        if measured != expected_digest:
            raise SystemExit(
                f"STEP8B22_SEALED_BLOB_MISMATCH={path.relative_to(ROOT)}/{measured}"
            )
    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    audit_import = "import YangMills.RG.BalabanCMP99FlatFiniteGridAliasingAudit"
    if audit_import not in core:
        raise SystemExit("STEP8B22_AUDIT_NOT_IN_CORE")
    for relative in (
        "docs/HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md",
        "docs/VERIFICATION-LEDGER.md",
    ):
        text = (ROOT / relative).read_text(encoding="utf-8")
        if STEP8B22_RUN not in text or STEP8B22_SOURCE not in text:
            raise SystemExit(f"STEP8B22_EVIDENCE_IDENTITY_MISSING={relative}")


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
    require_step8b22_sealed()
    promotion = plan()
    if not args.write:
        print(
            "STEP8B23_AE_PROMOTION_DRY_RUN_OK "
            f"head={actual} files=36 manifest={EXPECTED_DIGEST}"
        )
        return 0

    for target, content in promotion:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in promotion:
        if target.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(
        "STEP8B23_AE_PROMOTION_WRITE_OK "
        f"base_head={actual} files=36 manifest={EXPECTED_DIGEST}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
