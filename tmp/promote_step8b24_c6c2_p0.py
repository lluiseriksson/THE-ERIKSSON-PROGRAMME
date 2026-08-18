#!/usr/bin/env python3
"""Fail-closed promotion of the first C6c.2 P0 source/audit pair.

The script is read-only unless ``--write`` is supplied.  It deliberately
promotes only P0: later P0--P5 sources may not enter the tracked tree until
their immediate predecessor has elaborated and its axiom audit has run.
Step 8b.22 must already be cold-sealed, including its core/map/ledger record,
and a write additionally requires a fail-closed audit of the immutable P0--P9
Colab transcript.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
PREVIEW = runpy.run_path(str(TMP / "audit_p0_p5_promotion_preview.py"))
NOTEBOOK_AUDIT = runpy.run_path(str(TMP / "audit_p0_p9_executed_notebook.py"))
P0_FILES = (
    TMP / "P0CanonicalPrefixTower.lean",
    TMP / "P0CanonicalPrefixTowerAudit.lean",
)
EXPECTED_P0_DIGEST = (
    "CCF1079CA2667310176146993CE75AB66DF7B42C65E1970E9997B5A02BA67146"
)
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


def promotion_plan() -> list[tuple[Path, bytes]]:
    targets = PREVIEW["complete_target_map"]()
    names = PREVIEW["declaration_map"]()
    listed = [
        ROOT / line
        for line in (TMP / "P0-P5-SCRATCH-PATHS.txt")
        .read_text(encoding="utf-8-sig")
        .splitlines()
        if line
    ]
    PREVIEW["verify_raw_scope"](listed)

    result: list[tuple[Path, bytes]] = []
    rows: list[str] = []
    for source in P0_FILES:
        content, _ = PREVIEW["transform"](source, targets, names)
        target = targets[source]
        if target.exists():
            raise SystemExit(
                f"P0_PROMOTION_TARGET_ALREADY_EXISTS={target.relative_to(ROOT)}"
            )
        result.append((target, content))
        rows.append(
            f"{hashlib.sha256(content).hexdigest()}  "
            f"{target.relative_to(ROOT).as_posix()}\n"
        )
    digest = sha256("".join(rows).encode("utf-8"))
    if digest != EXPECTED_P0_DIGEST:
        raise SystemExit(f"P0_PROMOTION_DIGEST_MISMATCH={digest}")
    return result


def require_step8b22_sealed() -> None:
    for path, expected in STEP8B22_PAIR:
        measured = sha256(path.read_bytes())
        if measured != expected:
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
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    head = git("rev-parse", "HEAD")
    if head != args.expected_head:
        raise SystemExit(f"HEAD_MISMATCH={head}")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--quiet"], cwd=ROOT
    ).returncode:
        raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--cached", "--quiet"],
        cwd=ROOT,
    ).returncode:
        raise SystemExit("INDEX_NOT_CLEAN")

    require_step8b22_sealed()
    rows = promotion_plan()
    if not args.write:
        print(
            "STEP8B24_C6C2_P0_PROMOTION_DRY_RUN_OK "
            f"head={head} files={len(rows)} declarations=10 "
            f"manifest={EXPECTED_P0_DIGEST}"
        )
        return 0

    if args.evidence is None:
        raise SystemExit("P0_PROMOTION_EXECUTED_NOTEBOOK_REQUIRED")
    try:
        evidence_result = NOTEBOOK_AUDIT["audit"](args.evidence.resolve())
    except (OSError, UnicodeError, ValueError) as error:
        raise SystemExit(f"P0_PROMOTION_EXECUTED_NOTEBOOK_REJECTED={error}") from error
    print(evidence_result)

    for target, content in rows:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in rows:
        if target.read_bytes() != content:
            raise SystemExit(
                f"P0_PROMOTION_POST_WRITE_MISMATCH={target.relative_to(ROOT)}"
            )
    print(
        "STEP8B24_C6C2_P0_PROMOTION_WRITE_OK "
        f"base_head={head} files={len(rows)} declarations=10 "
        f"manifest={EXPECTED_P0_DIGEST}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
