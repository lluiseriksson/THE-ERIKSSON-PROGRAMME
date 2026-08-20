#!/usr/bin/env python3
"""Fail-closed promotion of the compiler-verified P0--P9 scratch chain.

The script is read-only unless ``--write`` is supplied.  A write requires the
exact v56 Colab PASS archive, preserves the already sealed P0 pair, requires
the already tracked P1 pair to equal the deterministic PRE-VALIDATION output,
and creates only the remaining 35 mapped targets.  It never removes a
PRE-VALIDATION mark: the promoted tracked graph needs its own cold validation
before a later seal may do that.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess

import audit_p0_p5_promotion_preview as preview
import audit_p0_p9_promotion as scope
import audit_p0_p9_v56_evidence as evidence_gate


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PROMOTED_MANIFEST_SHA256 = (
    "738FC4E57A9557F2F3769732C821F50BDE5FA7BF7110099335B70C1AD502FCD3"
)
P0_FILES = frozenset(
    {"P0CanonicalPrefixTower.lean", "P0CanonicalPrefixTowerAudit.lean"}
)
P1_FILES = frozenset(
    {"P1CoefficientMonotonicity.lean", "P1CoefficientMonotonicityAudit.lean"}
)


def configure_preview() -> None:
    preview.scope = scope
    preview.PATHS = ROOT / "tmp" / "P0-P9-SCRATCH-PATHS.txt"
    preview.RAW_MANIFEST = ROOT / "tmp" / "P0-P9-SCRATCH-MANIFEST.sha256"
    preview.EXPECTED_RAW_MANIFEST_SHA256 = evidence_gate.MANIFEST_SHA256
    preview.SCOPE_LABEL = "P0_P9"
    preview.EXPECTED_DECLARATIONS = 181
    preview.EXPECTED_PROMOTED_MODULES = 39


def git(*args: str) -> str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit("GIT_FAIL " + " ".join(args) + "\n" + child.stderr)
    return child.stdout.strip()


def visible(text: str) -> list[str]:
    return [line for line in preview.VISIBLE_LINES(text) if line.strip()]


def promotion_plan() -> tuple[list[tuple[Path, bytes]], int, int]:
    configure_preview()
    targets = preview.complete_target_map()
    names = preview.declaration_map()
    listed = [
        ROOT / line
        for line in preview.PATHS.read_text(encoding="utf-8-sig").splitlines()
        if line
    ]
    preview.verify_raw_scope(listed)
    if set(listed) != set(targets) or len(listed) != 39:
        raise SystemExit("P0_P9_PROMOTION_SCOPE_DRIFT")

    rows: list[str] = []
    writes: list[tuple[Path, bytes]] = []
    preserved = 0
    for source in listed:
        content, _ = preview.transform(source, targets, names)
        target = targets[source]
        rows.append(
            f"{hashlib.sha256(content).hexdigest()}  "
            f"{target.relative_to(ROOT).as_posix()}\n"
        )
        if source.name in P0_FILES:
            if not target.is_file():
                raise SystemExit(
                    f"P0_P9_SEALED_P0_MISSING={target.relative_to(ROOT)}"
                )
            tracked = target.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
            if visible(tracked) != visible(content.decode("utf-8")):
                raise SystemExit(
                    f"P0_P9_SEALED_P0_VISIBLE_DRIFT={target.relative_to(ROOT)}"
                )
            if "PRE-VALIDATION" in tracked:
                raise SystemExit(
                    f"P0_P9_SEALED_P0_MARK_REGRESSION={target.relative_to(ROOT)}"
                )
            preserved += 1
            continue
        if source.name in P1_FILES:
            if not target.is_file() or target.read_bytes() != content:
                raise SystemExit(
                    f"P0_P9_TRACKED_P1_BYTE_DRIFT={target.relative_to(ROOT)}"
                )
            preserved += 1
            continue
        if target.exists() and target.read_bytes() != content:
            raise SystemExit(
                f"P0_P9_PROMOTION_TARGET_DIVERGES={target.relative_to(ROOT)}"
            )
        writes.append((target, content))

    digest = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    if digest != EXPECTED_PROMOTED_MANIFEST_SHA256:
        raise SystemExit(f"P0_P9_PROMOTION_MANIFEST_DRIFT={digest}")
    if preserved != 4 or len(writes) != 35:
        raise SystemExit(
            f"P0_P9_PROMOTION_CARDINALITY_DRIFT=preserved:{preserved}/writes:{len(writes)}"
        )
    return writes, preserved, len(names)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    head = git("rev-parse", "HEAD")
    if head != args.expected_head:
        raise SystemExit(f"HEAD_MISMATCH={head}")
    for diff_args, label in (
        (("diff", "--quiet"), "TRACKED_WORKTREE_NOT_CLEAN"),
        (("diff", "--cached", "--quiet"), "INDEX_NOT_CLEAN"),
    ):
        child = subprocess.run(
            ["git", "-c", "safe.directory=*", *diff_args], cwd=ROOT
        )
        if child.returncode:
            raise SystemExit(label)

    writes, preserved, renamed = promotion_plan()
    if not args.write:
        print(
            "STEP8B24_C6C2_P0_P9_PROMOTION_DRY_RUN_OK "
            f"head={head} preserved={preserved} writes={len(writes)} "
            f"renamed={renamed} manifest={EXPECTED_PROMOTED_MANIFEST_SHA256}"
        )
        return 0
    if args.evidence is None:
        raise SystemExit("P0_P9_PROMOTION_EVIDENCE_REQUIRED")
    try:
        result = evidence_gate.audit(args.evidence.resolve())
    except (OSError, UnicodeError, ValueError) as error:
        raise SystemExit(f"P0_P9_PROMOTION_EVIDENCE_REJECTED={error}") from error
    print(result)

    for target, content in writes:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in writes:
        if target.read_bytes() != content:
            raise SystemExit(
                f"P0_P9_PROMOTION_POST_WRITE_MISMATCH={target.relative_to(ROOT)}"
            )
    print(
        "STEP8B24_C6C2_P0_P9_PROMOTION_WRITE_OK "
        f"base_head={head} preserved={preserved} writes={len(writes)} "
        f"renamed={renamed} manifest={EXPECTED_PROMOTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
