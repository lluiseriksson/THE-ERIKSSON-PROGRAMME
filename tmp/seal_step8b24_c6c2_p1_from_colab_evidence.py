#!/usr/bin/env python3
"""Seal the public Step 8b.24/C6c.2 P1 pair from one fresh-Colab notebook.

Default mode is read-only.  ``--write`` removes exactly the two P1
PRE-VALIDATION paragraphs, imports the sibling audit into ``YangMillsCore``
and records the immutable transcript hashes.  P2--P9 and all terminal
obligations remain outside this seal.
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
AUDIT = runpy.run_path(
    str(ROOT / "tmp" / "audit_step8b24_c6c2_p1_executed_notebook.py")
)
BASE = runpy.run_path(
    str(ROOT / "tmp" / "audit_step8b24_c6c2_p0_executed_notebook.py")
)

SOURCE_SHA = AUDIT["SOURCE_SHA"]
RUNNER_REV = AUDIT["RUNNER_REV"]
RUNNER_SHA256 = AUDIT["RUNNER_SHA256"]
SOURCE_STAGE = AUDIT["SOURCE_STAGE"]
AUDIT_STAGE = AUDIT["AUDIT_STAGE"]
AXIOM_HEADERS = AUDIT["AXIOM_HEADERS"]
SOURCE = ROOT / "YangMills" / "RG" / "BalabanCMP99SourcePrefixPoincare.lean"
SOURCE_AUDIT = (
    ROOT / "YangMills" / "RG" / "BalabanCMP99SourcePrefixPoincareAudit.lean"
)
CORE = ROOT / "YangMillsCore.lean"
MAP = ROOT / "docs" / "HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md"
LEDGER = ROOT / "docs" / "VERIFICATION-LEDGER.md"

PRE_VALIDATION = (
    b"PRE-VALIDATION: this module's source is present, its `.olean` has not yet\n"
    b"been materialized, and its result has not yet been verified by the compiler.\n"
)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


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


def git_blob(commit: str, relative: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "cat-file", "blob", f"{commit}:{relative}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit(
            f"GIT_BLOB_FAIL={commit}:{relative}\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout


def transcript(path: Path) -> dict[str, object]:
    verdict = AUDIT["audit"](path)
    payload = path.read_bytes()
    notebook = json.loads(payload.decode("utf-8"))
    text, evidenced = BASE["output_text"](notebook)
    if evidenced != 1:
        raise SystemExit(f"P1_EXECUTED_CELL_COUNT={evidenced}")
    rows = {
        stage: (int(exit_code), float(seconds))
        for stage, exit_code, seconds in re.findall(
            r"STAGE=([a-z0-9_]+) EXIT=([-0-9]+) SECONDS=([0-9]+(?:\.[0-9]+)?)",
            text,
        )
    }
    if rows.get(SOURCE_STAGE, (1, 0.0))[0] != 0:
        raise SystemExit("P1_FOCAL_NOT_GREEN")
    if rows.get(AUDIT_STAGE, (1, 0.0))[0] != 0:
        raise SystemExit("P1_AUDIT_NOT_GREEN")
    focal = BASE["stage_output"](text, SOURCE_STAGE)
    jobs = re.findall(r"Build completed successfully \(([0-9]+) jobs\)\.", focal)
    if len(jobs) != 1:
        raise SystemExit("P1_UNIQUE_FOCAL_JOB_COUNT_NOT_PROVED")
    fields = dict(re.findall(r"([a-z_]+)=([0-9a-f]{64})", verdict))
    required = {"evidence_sha256", "archive_sha256", "notebook_sha256"}
    if not required.issubset(fields):
        raise SystemExit(f"P1_AUDIT_HASH_FIELDS_MISSING={verdict}")
    return {
        "verdict": verdict,
        "jobs": int(jobs[0]),
        "focal_seconds": rows[SOURCE_STAGE][1],
        "audit_seconds": rows[AUDIT_STAGE][1],
        **fields,
    }


def sealed_pair() -> list[tuple[Path, bytes]]:
    result: list[tuple[Path, bytes]] = []
    for path in (SOURCE, SOURCE_AUDIT):
        relative = path.relative_to(ROOT).as_posix()
        raw = path.read_bytes()
        validated = git_blob(SOURCE_SHA, relative)
        if raw != validated:
            raise SystemExit(f"P1_VALIDATED_SOURCE_DRIFT={relative}/{sha256(raw)}")
        if raw.count(PRE_VALIDATION) != 1:
            raise SystemExit(f"P1_PRE_VALIDATION_SCOPE_MISMATCH={relative}")
        sealed = raw.replace(PRE_VALIDATION, b"", 1)
        if b"PRE-VALIDATION" in sealed:
            raise SystemExit(f"P1_STALE_PRE_VALIDATION={relative}")
        result.append((path, sealed))
    return result


def map_section(meta: dict[str, object]) -> bytes:
    return f"""

### Step 8b.24/C6c.2 P1 prefix-Poincare monotonicity (SEALED; P2 next)

One fresh Colab Pro+ CPU/high-RAM clone validated exact source
`{SOURCE_SHA}` under runner `{RUNNER_REV}` (runner SHA-256
`{RUNNER_SHA256}`).  The public P1 focal exited `0` after
`{meta['focal_seconds']:.3f} s` with `{meta['jobs']}` jobs and its eight-readout
audit exited `0` after `{meta['audit_seconds']:.3f} s`.  Every readout was a
subset of `{{propext, Classical.choice, Quot.sound}}`; `FINAL_STATUS=PASS`.
Independent transcript validation is recorded in ledger Addendum 870.

P1 proves monotonicity/positivity of the generated Poincare ledgers and the
retained-prefix smallness consequence.  It does not construct P2--P9, the
CMP96 Dirichlet defect, a uniform CMP99 (3.42) pair, the regional actions,
window 15, a terminal field or a `TermSource`.  Counters remain exactly
`20/41`, `TermSource = 0`; window 15 remains compatible but unattained.
""".encode("utf-8")


def ledger_addendum(meta: dict[str, object]) -> bytes:
    return f"""

## Addendum 870 (2026-08-19, **Step 8b.24/C6c.2 prefix-Poincare P1 sealed in fresh Colab checkout; 20/41 unchanged**)

Fresh Colab Pro+ CPU/high-RAM validation checked exact source `{SOURCE_SHA}`
with runner revision `{RUNNER_REV}` and runner SHA-256 `{RUNNER_SHA256}`.
The public `BalabanCMP99SourcePrefixPoincare` focal exited `0` after
`{meta['focal_seconds']:.3f} s` with `Build completed successfully
({meta['jobs']} jobs).`; its sibling audit exited `0` after
`{meta['audit_seconds']:.3f} s`.  All {AXIOM_HEADERS} declarations used only
`{{propext, Classical.choice, Quot.sound}}`.

The independent executed-notebook auditor accepted notebook SHA-256
`{meta['notebook_sha256']}`, evidence SHA-256 `{meta['evidence_sha256']}` and
reported archive SHA-256 `{meta['archive_sha256']}`.  This seal removes exactly
the two P1 PRE-VALIDATION marks and imports the sibling audit into
`YangMillsCore.lean`.  P2--P9 and every terminal obligation remain open;
counters stay exactly `20/41`, `TermSource = 0`, and window 15 remains
compatible but unattained.
""".encode("utf-8")


def seal_plan(meta: dict[str, object]) -> list[tuple[Path, bytes]]:
    pair = sealed_pair()
    core = CORE.read_bytes()
    anchor = b"import YangMills.RG.BalabanCMP99SourceCanonicalPrefixTowerAudit\n"
    addition = b"import YangMills.RG.BalabanCMP99SourcePrefixPoincareAudit\n"
    if core.count(anchor) != 1 or addition in core:
        raise SystemExit("P1_CORE_IMPORT_STATE_MISMATCH")
    core = core.replace(anchor, anchor + addition, 1)

    vertical = MAP.read_bytes()
    heading = b"### Step 8b.24/C6c.2 P1 prefix-Poincare monotonicity"
    if heading in vertical:
        raise SystemExit("P1_VERTICAL_SECTION_ALREADY_PRESENT")
    vertical += map_section(meta)

    ledger = LEDGER.read_bytes()
    if b"## Addendum 870 " in ledger or b"## Addendum 869 " not in ledger:
        raise SystemExit("P1_LEDGER_STATE_MISMATCH")
    ledger += ledger_addendum(meta)
    return [*pair, (CORE, core), (MAP, vertical), (LEDGER, ledger)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--executed-notebook", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    actual = git("rev-parse", "HEAD")
    if actual != args.expected_head:
        raise SystemExit(f"P1_HEAD_MISMATCH={actual}")
    if git("status", "--porcelain", "--untracked-files=no"):
        raise SystemExit("P1_TRACKED_WORKTREE_NOT_CLEAN")
    meta = transcript(args.executed_notebook)
    plan = seal_plan(meta)
    if not args.write:
        print(
            "STEP8B24_C6C2_P1_SEAL_PREVIEW_OK "
            f"head={actual} source={SOURCE_SHA} files={len(plan)} "
            f"notebook_sha256={meta['notebook_sha256']}"
        )
        for path, content in plan:
            print(f"{sha256(content)}  {path.relative_to(ROOT).as_posix()}")
        return 0
    for path, content in plan:
        path.write_bytes(content)
    for path, content in plan:
        if path.read_bytes() != content:
            raise SystemExit(f"P1_POST_WRITE_MISMATCH={path.relative_to(ROOT)}")
    print(f"STEP8B24_C6C2_P1_SEAL_WRITE_OK base_head={actual} files={len(plan)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(f"STEP8B24_C6C2_P1_SEAL_FAIL: {error}")
        raise SystemExit(1)
