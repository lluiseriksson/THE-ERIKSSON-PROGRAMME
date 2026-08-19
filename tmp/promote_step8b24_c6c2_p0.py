#!/usr/bin/env python3
"""Fail-closed promotion of the first C6c.2 P0 source/audit pair.

The script is read-only unless ``--write`` is supplied.  It deliberately
promotes only P0: later P0--P5 sources may not enter the tracked tree until
their immediate predecessor has elaborated and its axiom audit has run.
Step 8b.22 must already be cold-sealed, including its core/map/ledger record,
and a write additionally requires a fail-closed audit of the immutable P0--P9
Colab evidence archive.  A later stop-on-first-error is acceptable only after
the exact P0 source and its axiom audit have both passed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
PREVIEW = runpy.run_path(str(TMP / "audit_p0_p5_promotion_preview.py"))
ARCHIVE_AUDIT = runpy.run_path(str(TMP / "audit_p0_p9_evidence_archive.py"))
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
P0_SOURCE_STAGE = "p0_p9_01_p0canonicalprefixtower"
P0_AUDIT_STAGE = "p0_p9_02_p0canonicalprefixtoweraudit"
P0_AXIOM_HEADERS = 10
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
P0_EVIDENCE_IDENTITIES = {
    (
        "84eb07b5d1f2c3d7f245230a25846065b745a38e",
        "p0-p9-prefix-combes-thomas-v34",
    ),
    (
        "909a73cf87ff51486f9f460890a08f2efbe383ec",
        "p0-p9-prefix-combes-thomas-v35",
    ),
}


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


def require_p0_evidence(path: Path) -> str:
    """Accept a complete PASS or a later stop-on-first-error after P0 passed."""

    if P0_EVIDENCE_IDENTITIES != ARCHIVE_AUDIT["SUPPORTED_IDENTITIES"]:
        raise ValueError("P0 promoter/archive identity allowlists drifted")
    summary: str = ARCHIVE_AUDIT["audit"](path)
    members: dict[str, bytes] = ARCHIVE_AUDIT["read_regular_members"](path)
    root: str = ARCHIVE_AUDIT["EVIDENCE_ROOT"]
    evidence = json.loads(members[f"{root}/evidence.json"].decode("utf-8"))
    identity = (evidence.get("source_sha"), evidence.get("runner_rev"))
    if identity not in P0_EVIDENCE_IDENTITIES:
        raise ValueError(f"unsupported P0 evidence identity: {identity!r}")
    records = evidence["records"]
    by_stage = {record["stage"]: (index, record) for index, record in enumerate(records)}
    for stage in (P0_SOURCE_STAGE, P0_AUDIT_STAGE):
        if stage not in by_stage:
            raise ValueError(f"required P0 stage missing: {stage}")
        if by_stage[stage][1]["exit"] != 0:
            raise ValueError(f"required P0 stage failed: {stage}")
    if by_stage[P0_SOURCE_STAGE][0] >= by_stage[P0_AUDIT_STAGE][0]:
        raise ValueError("P0 source/audit order drift")

    audit_record = by_stage[P0_AUDIT_STAGE][1]
    audit_log = members[f"{root}/{audit_record['log']}"].decode("utf-8")
    compact = re.sub(r"\s+", "", audit_log)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != P0_AXIOM_HEADERS:
        raise ValueError(
            f"P0 axiom header count={len(blocks) + pure}, "
            f"expected={P0_AXIOM_HEADERS}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise ValueError(f"forbidden P0 axiom block {index}: {sorted(names)}")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise ValueError(f"forbidden P0 audit marker: {forbidden}")
    return summary + f" p0_axiom_headers={P0_AXIOM_HEADERS}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--executed-notebook", type=Path)
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

    supplied = int(args.evidence is not None) + int(args.executed_notebook is not None)
    if supplied != 1:
        raise SystemExit("P0_PROMOTION_EXACTLY_ONE_EVIDENCE_INPUT_REQUIRED")
    try:
        if args.evidence is not None:
            evidence_result = require_p0_evidence(args.evidence.resolve())
        else:
            assert args.executed_notebook is not None
            evidence_result = NOTEBOOK_AUDIT["audit_p0"](
                args.executed_notebook.resolve()
            )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        raise SystemExit(f"P0_PROMOTION_EVIDENCE_ARCHIVE_REJECTED={error}") from error
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
