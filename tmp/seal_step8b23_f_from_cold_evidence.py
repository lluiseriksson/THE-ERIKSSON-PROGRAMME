#!/usr/bin/env python3
"""Seal Step 8b.23 Unit F from one independently audited cold artifact.

The transformation is deliberately limited to the four Unit-F source/audit
pairs plus their core imports and the two durable ledgers.  Regional ``B0``,
window-15 attainment, terminal fields and ``TermSource`` remain out of scope.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path, PurePosixPath
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
F_GENERATOR = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b23_f_validation_runner.py")
)
COLD = runpy.run_path(str(ROOT / "tmp" / "audit_step8b23_f_cold_evidence.py"))
BASE = runpy.run_path(str(ROOT / "tmp" / "seal_step8b23_ae_from_colab_evidence.py"))

SOURCE_SHA = "fa29c350fd216305b56685b15a6aee3d80e46ae7"
BRICKS: tuple[tuple[str, int], ...] = F_GENERATOR["BRICKS"]
_, SOURCE_PATHS = F_GENERATOR["source_paths"]()
CORE = ROOT / "YangMillsCore.lean"
MAP = ROOT / "docs" / "HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md"
LEDGER = ROOT / "docs" / "VERIFICATION-LEDGER.md"

PRE_VALIDATION: bytes = BASE["PRE_VALIDATION"]
STATIC_DRAFT: bytes = BASE["STATIC_DRAFT"]
STATIC_SEALED: bytes = BASE["STATIC_SEALED"]
AUDIT_DRAFT: bytes = BASE["AUDIT_DRAFT"]
AUDIT_SEALED: bytes = BASE["AUDIT_SEALED"]


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def git(*args: str, binary: bool = False) -> bytes | str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit(
            "GIT_FAIL " + " ".join(args) + "\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout if binary else child.stdout.decode("utf-8").strip()


def validated_blob(relative: str) -> bytes:
    return git("cat-file", "blob", f"{SOURCE_SHA}:{relative}", binary=True)  # type: ignore[return-value]


def sealed_sources() -> list[tuple[Path, bytes]]:
    plan: list[tuple[Path, bytes]] = []
    source_marks = 0
    audit_marks = 0
    for relative in SOURCE_PATHS:
        path = ROOT / PurePosixPath(relative)
        raw = path.read_bytes()
        if raw != validated_blob(relative):
            raise SystemExit(f"VALIDATED_SOURCE_DRIFT={relative}/{sha256(raw)}")
        if raw.count(PRE_VALIDATION) != 1:
            raise SystemExit(f"PRE_VALIDATION_BLOCK_SCOPE_MISMATCH={relative}")
        sealed = raw.replace(PRE_VALIDATION, b"", 1)
        if STATIC_DRAFT in sealed:
            if sealed.count(STATIC_DRAFT) != 1:
                raise SystemExit(f"STATIC_DRAFT_SCOPE_MISMATCH={relative}")
            sealed = sealed.replace(STATIC_DRAFT, STATIC_SEALED, 1)
            source_marks += 1
        if AUDIT_DRAFT in sealed:
            if sealed.count(AUDIT_DRAFT) != 1:
                raise SystemExit(f"AUDIT_DRAFT_SCOPE_MISMATCH={relative}")
            sealed = sealed.replace(AUDIT_DRAFT, AUDIT_SEALED, 1)
            audit_marks += 1
        if b"PRE-VALIDATION" in sealed or b"NOT COMPILER-VERIFIED" in sealed:
            raise SystemExit(f"STALE_VALIDATION_MARK_SURVIVES={relative}")
        plan.append((path, sealed))
    if len(plan) != 8 or source_marks != 4 or audit_marks != 4:
        raise SystemExit(
            f"UNIT_F_SEAL_SCOPE_MISMATCH={len(plan)}/{source_marks}/{audit_marks}"
        )
    return plan


def audit_imports() -> list[bytes]:
    return [
        f"import YangMills.RG.{module}Audit\n".encode()
        for module, _ in BRICKS
    ]


def aggregate_seconds(result: dict[str, object]) -> int:
    stages = result.get("stages")
    if not isinstance(stages, dict) or len(stages) != 8:
        raise SystemExit("UNIT_F_COLD_STAGE_SCOPE_MISMATCH")
    total = 0
    for stage, row in stages.items():
        if not isinstance(stage, str) or not isinstance(row, dict):
            raise SystemExit("UNIT_F_COLD_STAGE_ROW_MALFORMED")
        if row.get("exit") != 0 or not isinstance(row.get("seconds"), int):
            raise SystemExit(f"UNIT_F_COLD_STAGE_NOT_GREEN={stage}")
        total += int(row["seconds"])
    return total


def map_section(result: dict[str, object], run_id: str, run_url: str) -> bytes:
    seconds = aggregate_seconds(result)
    return f"""

### Step 8b.23 Unit F: post-aliasing periodic owner decay (SEALED; cold checkout; 20/41 unchanged)

The four Unit-F bricks from the centered periodic residue sum through the
diagonal finite Green owner bound have been compiled and audited together.
The route retains exponential decay in the centered periodic representative
without a volume factor and installs the exact endpoint and zero-residue
dictionaries used by the diagonal Gate-7 carrier.

One cold GitHub Actions checkout validated exact source `{SOURCE_SHA}` in
terminal run `{run_id}` ({run_url}).  All eight focal/audit stages exited `0`
in {seconds} aggregate stage-seconds.  The four audits emitted exactly 49
axiom blocks, each a subset of `{{propext, Classical.choice, Quot.sound}}`;
the artifact contains literal `FINAL_STATUS=PASS`.  Inner archive SHA-256 is
`{result['inner_archive_sha256']}` and raw outer artifact ZIP SHA-256 is
`{result['outer_artifact_zip_sha256']}`.

This is the Unit-F periodic-owner seal only, not the independent-scale
regional `B0` dictionary and not window-15 attainment.  No terminal field is
discharged and no `TermSource` inhabitant is constructed.  Counters remain
exactly `20/41`, `TermSource = 0`.
""".encode()


def ledger_addendum(result: dict[str, object], run_id: str, run_url: str) -> bytes:
    seconds = aggregate_seconds(result)
    return f"""

## Addendum 870 (2026-08-20, **Step 8b.23 Unit F sealed from one cold terminal checkout; 20/41 unchanged**)

One cold GitHub Actions checkout compiled and audited the complete four-brick
Unit-F queue at exact source `{SOURCE_SHA}` in run `{run_id}` ({run_url}).
All eight focal/audit stages exited `0` in {seconds} aggregate stage-seconds;
all 49 measured axiom blocks are subsets of
`{{propext, Classical.choice, Quot.sound}}`, and the retained artifact has
literal `FINAL_STATUS=PASS`.

The independent validator checked the 44 exact source/prerequisite blobs,
the cold checkout and source/Mathlib/toolchain identities, stage order,
literal build sentinels, every axiom block, the inner archive and the raw
outer ZIP.  Inner archive SHA-256 is `{result['inner_archive_sha256']}`; raw
outer artifact ZIP SHA-256 is `{result['outer_artifact_zip_sha256']}`.

This seal removes validation marks only from the eight Unit-F files and
imports their four audits into `YangMillsCore.lean`.  Regional `B0`, the
independent-scale owner dictionary, attainment of window 15, terminal fields
and a `TermSource` inhabitant remain open.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.
""".encode()


def seal_plan(
    result: dict[str, object], run_id: str, run_url: str
) -> list[tuple[Path, bytes]]:
    sources = sealed_sources()
    core = CORE.read_bytes()
    imports = audit_imports()
    if any(item in core for item in imports):
        raise SystemExit("UNIT_F_AUDIT_ALREADY_IN_CORE")
    anchor = b"import YangMills.RG.BalabanCMP99PhysicalGreenFiniteGridAliasingAudit\n"
    if core.count(anchor) != 1:
        raise SystemExit("UNIT_F_CORE_ANCHOR_MISMATCH")
    core = core.replace(anchor, anchor + b"".join(imports), 1)

    vertical = MAP.read_bytes()
    section_anchor = b"### Step 8b.23 Unit F:"
    if section_anchor in vertical:
        raise SystemExit("UNIT_F_VERTICAL_SECTION_ALREADY_PRESENT")
    vertical += map_section(result, run_id, run_url)

    ledger = LEDGER.read_bytes()
    if b"## Addendum 870 " in ledger or b"## Addendum 869 " not in ledger:
        raise SystemExit("UNIT_F_LEDGER_STATE_MISMATCH")
    ledger += ledger_addendum(result, run_id, run_url)
    return [*sources, (CORE, core), (MAP, vertical), (LEDGER, ledger)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--artifact-root", required=True, type=Path)
    parser.add_argument("--outer-zip", required=True, type=Path)
    parser.add_argument("--workflow-sha", required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--run-url", required=True)
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

    result: dict[str, object] = COLD["validate"](
        args.artifact_root, args.outer_zip, SOURCE_SHA, args.workflow_sha
    )
    plan = seal_plan(result, args.run_id, args.run_url)
    if not args.write:
        print(
            "STEP8B23_F_COLD_SEAL_PREVIEW_OK "
            f"head={actual} source={SOURCE_SHA} files={len(plan)} "
            f"inner_sha256={result['inner_archive_sha256']} "
            f"outer_sha256={result['outer_artifact_zip_sha256']}"
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
        "STEP8B23_F_COLD_SEAL_WRITE_OK "
        f"base_head={actual} files={len(plan)} "
        f"outer_sha256={result['outer_artifact_zip_sha256']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError, ValueError) as error:
        print(f"STEP8B23_F_COLD_SEAL_FAIL: {error}")
        raise SystemExit(1)
