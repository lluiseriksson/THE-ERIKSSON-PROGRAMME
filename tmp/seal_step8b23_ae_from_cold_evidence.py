#!/usr/bin/env python3
"""Seal Step 8b.23 Units A--E from one independently audited cold artifact.

This is the GitHub-Actions counterpart of the Colab archive sealer.  It is
read-only unless ``--write`` is supplied and reuses the same exact 36-file
source transformation.  Unit F and every terminal counter remain out of
scope.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
BASE = runpy.run_path(str(ROOT / "tmp" / "seal_step8b23_ae_from_colab_evidence.py"))
COLD = runpy.run_path(str(ROOT / "tmp" / "audit_step8b23_ae_cold_evidence.py"))

SOURCE_SHA: str = BASE["SOURCE_SHA"]
EXPECTED_AXIOMS: int = BASE["EXPECTED_AXIOMS"]
CORE: Path = BASE["CORE"]
MAP: Path = BASE["MAP"]
LEDGER: Path = BASE["LEDGER"]


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


def aggregate_seconds(result: dict[str, object]) -> int:
    stages = result.get("stages")
    if not isinstance(stages, dict) or len(stages) != 36:
        raise SystemExit("A_E_COLD_STAGE_SCOPE_MISMATCH")
    total = 0
    for stage, row in stages.items():
        if not isinstance(stage, str) or not isinstance(row, dict):
            raise SystemExit("A_E_COLD_STAGE_ROW_MALFORMED")
        if row.get("exit") != 0 or not isinstance(row.get("seconds"), int):
            raise SystemExit(f"A_E_COLD_STAGE_NOT_GREEN={stage}")
        total += int(row["seconds"])
    return total


def map_section(
    result: dict[str, object], run_id: str, run_url: str
) -> bytes:
    seconds = aggregate_seconds(result)
    return f"""

### Step 8b.23: source-specific physical Green Fourier route, Units A--E (SEALED; cold checkout; 20/41 unchanged)

The eighteen ordered bricks from the centered Brillouin/torus dictionary
through the literal physical finite-grid aliasing endpoint have been compiled
and audited together.  The route constructs the common mass-uniform strip,
the signed product-contour displacement, normalized Green bounds, the exact
torus coefficient dictionary, absolute Fourier summability and the
source-specific Step-8b.22 consumer.  No free Fourier-series identity is
accepted at the endpoint.

One cold GitHub Actions checkout validated exact source `{SOURCE_SHA}` in
terminal run `{run_id}` ({run_url}).  All 36 focal/audit stages exited `0` in
{seconds} aggregate stage-seconds.  The 18 audits emitted exactly
{EXPECTED_AXIOMS} axiom blocks, each a subset of
`{{propext, Classical.choice, Quot.sound}}`; the artifact contains literal
`FINAL_STATUS=PASS`.  Inner archive SHA-256 is
`{result['inner_archive_sha256']}` and raw outer artifact ZIP SHA-256 is
`{result['outer_artifact_zip_sha256']}`.

This is a source-specific A--E seal, not Unit F and not regional `B0`.
Window 15 is still compatible but unattained; no terminal field is discharged
and no `TermSource` inhabitant is constructed.  Counters remain exactly
`20/41`, `TermSource = 0`.
""".encode("utf-8")


def ledger_addendum(
    result: dict[str, object], run_id: str, run_url: str
) -> bytes:
    seconds = aggregate_seconds(result)
    return f"""

## Addendum 868 (2026-08-19, **Step 8b.23 Units A--E sealed from one cold terminal checkout; 20/41 unchanged**)

One cold GitHub Actions checkout compiled and audited the complete 18-brick
A--E queue at exact source `{SOURCE_SHA}` in run `{run_id}` ({run_url}).
All 36 focal/audit stages exited `0` in {seconds} aggregate stage-seconds;
all {EXPECTED_AXIOMS} measured axiom blocks are subsets of
`{{propext, Classical.choice, Quot.sound}}`, and the retained artifact has
literal `FINAL_STATUS=PASS`.

The independent validator reconstructed all 36 validated Git blobs, checked
the cold checkout and exact source/Mathlib/toolchain identities, stage order,
literal build sentinels, every axiom block, the inner archive and the raw
outer ZIP.  Inner archive SHA-256 is `{result['inner_archive_sha256']}`; raw
outer artifact ZIP SHA-256 is `{result['outer_artifact_zip_sha256']}`.

This seal removes validation marks only from the 36 A--E files and imports
their 18 audits into `YangMillsCore.lean`.  Unit F, regional `B0`, attainment
of window 15, terminal fields and a `TermSource` inhabitant remain open.
Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.
""".encode("utf-8")


def seal_plan(
    result: dict[str, object], run_id: str, run_url: str
) -> list[tuple[Path, bytes]]:
    sources, _, _ = BASE["sealed_sources"]()

    core = CORE.read_bytes()
    imports: list[bytes] = BASE["audit_imports"]()
    if any(item in core for item in imports):
        raise SystemExit("A_E_AUDIT_ALREADY_IN_CORE")
    anchor = b"import YangMills.RG.BalabanCMP99FlatFiniteGridAliasingAudit\n"
    if core.count(anchor) != 1:
        raise SystemExit("A_E_CORE_ANCHOR_MISMATCH")
    core = core.replace(anchor, anchor + b"".join(imports), 1)

    vertical = MAP.read_bytes()
    if b"### Step 8b.23:" in vertical:
        raise SystemExit("A_E_VERTICAL_SECTION_ALREADY_PRESENT")
    vertical += map_section(result, run_id, run_url)

    ledger = LEDGER.read_bytes()
    if b"## Addendum 868 " in ledger or b"## Addendum 867 " not in ledger:
        raise SystemExit("A_E_LEDGER_STATE_MISMATCH")
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
        args.artifact_root,
        args.outer_zip,
        SOURCE_SHA,
        args.workflow_sha,
    )
    plan = seal_plan(result, args.run_id, args.run_url)
    if not args.write:
        print(
            "STEP8B23_AE_COLD_SEAL_PREVIEW_OK "
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
        "STEP8B23_AE_COLD_SEAL_WRITE_OK "
        f"base_head={actual} files={len(plan)} "
        f"outer_sha256={result['outer_artifact_zip_sha256']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError, ValueError) as error:
        print(f"STEP8B23_AE_COLD_SEAL_FAIL: {error}")
        raise SystemExit(1)
