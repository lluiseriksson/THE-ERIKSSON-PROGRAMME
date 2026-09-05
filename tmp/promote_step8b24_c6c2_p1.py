#!/usr/bin/env python3
"""Promote only the P1 prefix-Poincare pair after P0 has been sealed."""

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
PREVIEW = runpy.run_path(str(TMP / "audit_p0_p5_promotion_preview.py"))
TRANSCRIPT = runpy.run_path(str(TMP / "audit_p0_p9_executed_notebook.py"))
FILES = (
    TMP / "P1CoefficientMonotonicity.lean",
    TMP / "P1CoefficientMonotonicityAudit.lean",
)
EXPECTED_MANIFEST = "9D2EEF16C5DF7CADA2F71B04B47AA61AB08EDD72DFEB6AF6CEDD376448857EA7"
P0_SOURCE = ROOT / "YangMills/RG/BalabanCMP99SourceCanonicalPrefixTower.lean"
P0_AUDIT = ROOT / "YangMills/RG/BalabanCMP99SourceCanonicalPrefixTowerAudit.lean"


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


def plan() -> list[tuple[Path, bytes]]:
    targets = PREVIEW["complete_target_map"]()
    names = PREVIEW["declaration_map"]()
    result: list[tuple[Path, bytes]] = []
    rows: list[str] = []
    for source in FILES:
        content, _ = PREVIEW["transform"](source, targets, names)
        target = targets[source]
        if target.exists() and target.read_bytes() != content:
            raise SystemExit(f"P1_PROMOTION_TARGET_DIVERGES={target.relative_to(ROOT)}")
        result.append((target, content))
        rows.append(
            f"{hashlib.sha256(content).hexdigest()}  "
            f"{target.relative_to(ROOT).as_posix()}\n"
        )
    measured = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    if measured != EXPECTED_MANIFEST:
        raise SystemExit(f"P1_PROMOTION_MANIFEST_MISMATCH={measured}")
    return result


def require_p0_sealed() -> None:
    for path in (P0_SOURCE, P0_AUDIT):
        if not path.is_file():
            raise SystemExit(f"P0_SEALED_FILE_MISSING={path.relative_to(ROOT)}")
        if b"PRE-VALIDATION:" in path.read_bytes():
            raise SystemExit(f"P0_STILL_PRE_VALIDATION={path.relative_to(ROOT)}")
    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    marker = "import YangMills.RG.BalabanCMP99SourceCanonicalPrefixTowerAudit"
    if marker not in core:
        raise SystemExit("P0_CORE_IMPORT_MISSING")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--executed-notebook", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    if git("rev-parse", "HEAD") != args.expected_head:
        raise SystemExit("P1_PROMOTION_HEAD_MISMATCH")
    if git("status", "--porcelain", "--untracked-files=no"):
        raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    require_p0_sealed()
    transcript = TRANSCRIPT["audit_p1"](args.executed_notebook)
    outputs = plan()
    if args.write:
        for target, content in outputs:
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                target.write_bytes(content)
        if git("rev-parse", "HEAD") != args.expected_head:
            raise SystemExit("P1_PROMOTION_HEAD_MOVED_DURING_WRITE")
        mode = "WRITE"
    else:
        mode = "PREVIEW"
    print(
        f"STEP8B24_C6C2_P1_PROMOTION_{mode}_OK files={len(outputs)} "
        f"manifest={EXPECTED_MANIFEST} transcript=({transcript})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
