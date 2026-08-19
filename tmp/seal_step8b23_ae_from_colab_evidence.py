#!/usr/bin/env python3
"""Seal Step 8b.23 Units A--E from one validated fresh-Colab archive.

The default mode is read-only.  ``--write`` is accepted only with a clean
tracked tree, an exact caller-supplied HEAD, byte-identical validated source
blobs, a complete PASS archive, and the frozen 18-brick/124-readout scope.
Unit F and every terminal counter are deliberately outside this seal.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_AUDIT = runpy.run_path(
    str(ROOT / "tmp" / "audit_step8b23_ae_colab_archive.py")
)
GENERATOR = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_ae_validation_runner.py")
)
BASE_AUDIT = runpy.run_path(
    str(ROOT / "tmp" / "audit_p0_p9_evidence_archive.py")
)

SOURCE_SHA = ARCHIVE_AUDIT["SOURCE_SHA"]
RUNNER_REV = ARCHIVE_AUDIT["RUNNER_REV"]
RUNNER_COMMIT = "6d5e6cf37c62733daef4ddf57d13f2fe506a4773"
NOTEBOOK_COMMIT = "a421a186a181db55e85e3874798a8290be374917"
EVIDENCE_ROOT = ARCHIVE_AUDIT["EVIDENCE_ROOT"]
BRICKS: tuple[tuple[str, int], ...] = GENERATOR["BRICKS"]
SOURCE_PATHS: list[str] = GENERATOR["source_paths"]()
EXPECTED_AXIOMS = sum(count for _, count in BRICKS)

CORE = ROOT / "YangMillsCore.lean"
MAP = ROOT / "docs" / "HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md"
LEDGER = ROOT / "docs" / "VERIFICATION-LEDGER.md"

PRE_VALIDATION = (
    b"/-!\n"
    b"PRE-VALIDATION: this module's source is present, its `.olean` has not yet\n"
    b"been materialized, and its result has not yet been verified by the compiler.\n"
    b"-/\n"
)
STATIC_DRAFT = b"STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED."
STATIC_SEALED = b"SEALED SOURCE-SPECIFIC BRICK -- COMPILER-VERIFIED."
STATIC_AUDIT_DRAFT = (
    b"/- STATIC AUDIT DRAFT ONLY -- target module is not compiler-verified. -/"
)
STATIC_AUDIT_SEALED = b"/- SEALED AUDIT -- target module is compiler-verified. -/"
AUDIT_DRAFT = b"-- PRE-VALIDATION SCRATCH:"
AUDIT_SEALED = b"-- SEALED AXIOM SURFACE:"


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


def git_blob(commit: str, path: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "cat-file", "blob", f"{commit}:{path}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit(
            f"GIT_BLOB_FAIL={commit}:{path}\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout


def expected_queue() -> list[str]:
    result: list[str] = []
    for index, (module, _) in enumerate(BRICKS, start=1):
        slug = module.removeprefix("Balaban").lower()
        result.extend((f"{index:02d}_{slug}_focal", f"{index:02d}_{slug}_audit"))
    return result


def validated_archive(path: Path) -> tuple[dict[str, object], str, str]:
    verdict = ARCHIVE_AUDIT["audit"](path)
    if "status=PASS" not in verdict or "queue_stages=36" not in verdict:
        raise SystemExit(f"A_E_ARCHIVE_NOT_COMPLETE_PASS={verdict}")
    members = BASE_AUDIT["read_regular_members"](path)
    evidence_name = f"{EVIDENCE_ROOT}/evidence.json"
    evidence_raw = members.get(evidence_name)
    if evidence_raw is None:
        raise SystemExit("A_E_EVIDENCE_JSON_MISSING")
    evidence = json.loads(evidence_raw.decode("utf-8"))
    if evidence.get("status") != "PASS":
        raise SystemExit("A_E_EVIDENCE_STATUS_NOT_PASS")
    if evidence.get("source_sha") != SOURCE_SHA or evidence.get("runner_rev") != RUNNER_REV:
        raise SystemExit("A_E_EVIDENCE_IDENTITY_MISMATCH")
    queue = expected_queue()
    queue_records = [
        row for row in evidence.get("records", [])
        if isinstance(row, dict) and row.get("stage") in set(queue)
    ]
    if [row.get("stage") for row in queue_records] != queue:
        raise SystemExit("A_E_EVIDENCE_QUEUE_MISMATCH")
    if any(row.get("exit") != 0 for row in queue_records):
        raise SystemExit("A_E_EVIDENCE_NONZERO_QUEUE_STAGE")
    payload_hash = sha256(evidence_raw.removesuffix(b"\n"))
    return evidence, payload_hash, sha256(path.read_bytes())


def sealed_sources() -> tuple[list[tuple[Path, bytes]], int, int]:
    plan: list[tuple[Path, bytes]] = []
    static_count = 0
    static_audit_count = 0
    audit_note_count = 0
    for relative in SOURCE_PATHS:
        path = ROOT / PurePosixPath(relative)
        raw = path.read_bytes()
        validated = git_blob(SOURCE_SHA, relative)
        if raw != validated:
            raise SystemExit(f"VALIDATED_SOURCE_DRIFT={relative}/{sha256(raw)}")
        if raw.count(PRE_VALIDATION) != 1:
            raise SystemExit(f"PRE_VALIDATION_BLOCK_SCOPE_MISMATCH={relative}")
        sealed = raw.replace(PRE_VALIDATION, b"", 1)
        if STATIC_DRAFT in sealed:
            if sealed.count(STATIC_DRAFT) != 1:
                raise SystemExit(f"STATIC_DRAFT_SCOPE_MISMATCH={relative}")
            sealed = sealed.replace(STATIC_DRAFT, STATIC_SEALED, 1)
            static_count += 1
        if STATIC_AUDIT_DRAFT in sealed:
            if sealed.count(STATIC_AUDIT_DRAFT) != 1:
                raise SystemExit(f"STATIC_AUDIT_SCOPE_MISMATCH={relative}")
            sealed = sealed.replace(STATIC_AUDIT_DRAFT, STATIC_AUDIT_SEALED, 1)
            static_audit_count += 1
        if AUDIT_DRAFT in sealed:
            if sealed.count(AUDIT_DRAFT) != 1:
                raise SystemExit(f"AUDIT_DRAFT_SCOPE_MISMATCH={relative}")
            sealed = sealed.replace(AUDIT_DRAFT, AUDIT_SEALED, 1)
            audit_note_count += 1
        if b"PRE-VALIDATION" in sealed or b"NOT COMPILER-VERIFIED" in sealed:
            raise SystemExit(f"STALE_VALIDATION_MARK_SURVIVES={relative}")
        plan.append((path, sealed))
    if (
        len(plan) != 36
        or static_count != 18
        or static_audit_count != 4
        or audit_note_count != 14
    ):
        raise SystemExit(
            "A_E_SEAL_SCOPE_MISMATCH="
            f"{len(plan)}/static={static_count}/static_audit={static_audit_count}/"
            f"audit_note={audit_note_count}"
        )
    return plan, static_count, audit_note_count


def audit_imports() -> list[bytes]:
    return [
        f"import YangMills.RG.{module}Audit\n".encode("utf-8")
        for module, _ in BRICKS
    ]


def stage_summary(evidence: dict[str, object]) -> tuple[float, int]:
    queue = set(expected_queue())
    seconds = 0.0
    jobs = 0
    members = evidence.get("records")
    if not isinstance(members, list):
        raise SystemExit("A_E_RECORDS_MISSING")
    for row in members:
        if not isinstance(row, dict) or row.get("stage") not in queue:
            continue
        seconds += float(row.get("seconds", 0.0))
        stage = str(row.get("stage"))
        if stage.endswith("_focal"):
            log_name = row.get("log")
            if not isinstance(log_name, str):
                raise SystemExit(f"A_E_FOCAL_LOG_MISSING={stage}")
    return seconds, jobs


def map_section(
    evidence: dict[str, object], evidence_hash: str, archive_hash: str
) -> bytes:
    queue_seconds, _ = stage_summary(evidence)
    return f"""

### Step 8b.23: source-specific physical Green Fourier route, Units A--E (SEALED; fresh Colab; 20/41 unchanged)

The eighteen ordered bricks from the centered Brillouin/torus dictionary
through the literal physical finite-grid aliasing endpoint have been compiled
and audited together.  The route constructs the common mass-uniform strip,
the signed product-contour displacement, normalized Green bounds, the exact
torus coefficient dictionary, absolute Fourier summability and the
source-specific Step-8b.22 consumer.  No free Fourier-series identity is
accepted at the endpoint.

One fresh Colab Pro+ CPU/high-RAM clone validated exact source `{SOURCE_SHA}`
with runner `{RUNNER_REV}` (runner checkpoint `{RUNNER_COMMIT}`, notebook
checkpoint `{NOTEBOOK_COMMIT}`).  All 36 focal/audit stages exited `0` in
{queue_seconds:.3f} aggregate stage-seconds.  The 18 audits emitted exactly
{EXPECTED_AXIOMS} axiom blocks, each a subset of
`{{propext, Classical.choice, Quot.sound}}`; `FINAL_STATUS=PASS`.
Evidence JSON SHA-256 is `{evidence_hash}` and archive SHA-256 is
`{archive_hash}`.

This is a source-specific A--E seal, not Unit F and not regional `B0`.
Window 15 is still compatible but unattained; no terminal field is discharged
and no `TermSource` inhabitant is constructed.  Counters remain exactly
`20/41`, `TermSource = 0`.
""".encode("utf-8")


def ledger_addendum(
    evidence: dict[str, object], evidence_hash: str, archive_hash: str
) -> bytes:
    queue_seconds, _ = stage_summary(evidence)
    return f"""

## Addendum 869 (2026-08-19, **Step 8b.23 Units A--E sealed in one fresh Colab clone; 20/41 unchanged**)

One fresh Colab Pro+ CPU/high-RAM clone compiled and audited the complete
18-brick A--E queue at exact source `{SOURCE_SHA}` under runner
`{RUNNER_REV}`.  Runner checkpoint `{RUNNER_COMMIT}` and notebook checkpoint
`{NOTEBOOK_COMMIT}` bind the transport.  All 36 focal/audit stages exited `0`
in {queue_seconds:.3f} aggregate stage-seconds; all {EXPECTED_AXIOMS} measured
axiom blocks are subsets of `{{propext, Classical.choice, Quot.sound}}`, and
the retained archive has literal `FINAL_STATUS=PASS`.

Evidence JSON SHA-256 is `{evidence_hash}`; retained archive SHA-256 is
`{archive_hash}`.  The independent archive validator reconstructed all 38
validated Git blobs (36 source/audit files plus two Mathlib-only reproducers),
verified the frozen 36-stage queue, every retained log digest, stop-on-first-
error semantics and exact source/Mathlib/runner identity.

This seal removes validation marks only from the 36 A--E files and imports
their 18 audits into `YangMillsCore.lean`.  Unit F, regional `B0`, attainment
of window 15, terminal fields and a `TermSource` inhabitant remain open.
Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.
""".encode("utf-8")


def seal_plan(
    evidence: dict[str, object], evidence_hash: str, archive_hash: str
) -> list[tuple[Path, bytes]]:
    sources, _, _ = sealed_sources()

    core = CORE.read_bytes()
    imports = audit_imports()
    if any(item in core for item in imports):
        raise SystemExit("A_E_AUDIT_ALREADY_IN_CORE")
    anchor = b"import YangMills.RG.BalabanCMP99FlatFiniteGridAliasingAudit\n"
    if core.count(anchor) != 1:
        raise SystemExit("A_E_CORE_ANCHOR_MISMATCH")
    core = core.replace(anchor, anchor + b"".join(imports), 1)

    vertical = MAP.read_bytes()
    if b"### Step 8b.23:" in vertical:
        raise SystemExit("A_E_VERTICAL_SECTION_ALREADY_PRESENT")
    vertical += map_section(evidence, evidence_hash, archive_hash)

    ledger = LEDGER.read_bytes()
    if b"## Addendum 869 " in ledger or b"## Addendum 868 " not in ledger:
        raise SystemExit("A_E_LEDGER_STATE_MISMATCH")
    ledger += ledger_addendum(evidence, evidence_hash, archive_hash)
    return [*sources, (CORE, core), (MAP, vertical), (LEDGER, ledger)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--archive", required=True, type=Path)
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
        ["git", "-c", "safe.directory=*", "diff", "--cached", "--quiet"],
        cwd=ROOT,
    ).returncode != 0:
        raise SystemExit("INDEX_NOT_CLEAN")

    evidence, evidence_hash, archive_hash = validated_archive(args.archive)
    plan = seal_plan(evidence, evidence_hash, archive_hash)
    if not args.write:
        print(
            "STEP8B23_AE_SEAL_PREVIEW_OK "
            f"head={actual} source={SOURCE_SHA} files={len(plan)} "
            f"evidence_sha256={evidence_hash} archive_sha256={archive_hash}"
        )
        for path, content in plan:
            print(f"{sha256(content)}  {path.relative_to(ROOT).as_posix()}")
        return 0

    for path, content in plan:
        path.write_bytes(content)
    for path, content in plan:
        if path.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={path.relative_to(ROOT)}")
    print(
        "STEP8B23_AE_SEAL_WRITE_OK "
        f"base_head={actual} files={len(plan)} archive_sha256={archive_hash}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(f"STEP8B23_AE_SEAL_FAIL: {error}")
        raise SystemExit(1)
