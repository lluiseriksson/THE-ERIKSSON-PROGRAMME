#!/usr/bin/env python3
"""Prepare the exact Step 8b.22 seal from independently validated evidence.

The default is a read-only preview.  ``--write`` is accepted only at the exact
workflow HEAD with a clean tracked tree and after the complete artifact audit.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
AUDIT = runpy.run_path(str(ROOT / "tmp" / "audit_step8b22_cold_evidence.py"))
EXPECTED_HEAD = "b05ef65af97a95752d1c929e30749d886d425d8d"
RUN_ID = 31991954503
JOB_ID = 95276977132
RUN_URL = (
    "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/"
    f"actions/runs/{RUN_ID}"
)
SOURCE = ROOT / "YangMills" / "RG" / "BalabanCMP99FlatFiniteGridAliasing.lean"
AUDIT_SOURCE = (
    ROOT / "YangMills" / "RG" / "BalabanCMP99FlatFiniteGridAliasingAudit.lean"
)
CORE = ROOT / "YangMillsCore.lean"
MAP = ROOT / "docs" / "HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md"
LEDGER = ROOT / "docs" / "VERIFICATION-LEDGER.md"

RAW_HASHES = {
    SOURCE: "DE04CA53CE8B753E80514E607F0B47AE6C6CF41811B353E60030B21F4A5A2A52",
    AUDIT_SOURCE: "1207C5881C98379753407F426392100B08E44C503D64CE03CC2C3DABA7B5290B",
}
SEALED_HASHES = {
    SOURCE: "C82E0BB9D43BECE07C5660E7D3170F2289EBC4188969C222ABC6647C9F0EC34A",
    AUDIT_SOURCE: "9B804AFB964B08EED9A2B7910C8013F29BC326FAE5324C55F4130EB6F5A89785",
}
SOURCE_PRE = (
    b"PRE-VALIDATION: source present, `.olean` not yet materialized, and the result\n"
    b"has not yet been verified by the Lean compiler.\n\n"
)
AUDIT_PRE = (
    b"/-!\n"
    b"PRE-VALIDATION: source present, `.olean` not yet materialized, and the audit\n"
    b"has not yet been verified by the Lean compiler.\n"
    b"-/\n\n"
)
CORE_ANCHOR = b"import YangMills.RG.BalabanCMP89Eq251LatticePhasePeriodicityAudit\n"
CORE_IMPORT = b"import YangMills.RG.BalabanCMP99FlatFiniteGridAliasingAudit\n"
MAP_HEADER = (
    b"### Step 8b.22: exact finite-grid Fourier aliasing substrate "
    b"(PRE-VALIDATION; NOT CHECKED)\n"
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


def stage(result: dict[str, object], name: str) -> dict[str, object]:
    stages = result["stages"]
    if not isinstance(stages, dict) or name not in stages:
        raise SystemExit(f"MISSING_STAGE_RESULT={name}")
    row = stages[name]
    if not isinstance(row, dict):
        raise SystemExit(f"MALFORMED_STAGE_RESULT={name}")
    return row


def axiom_lines(result: dict[str, object]) -> str:
    axioms = result["axioms"]
    if not isinstance(axioms, list) or len(axioms) != 7:
        raise SystemExit("AXIOM_RESULT_SCOPE_MISMATCH")
    return "\n".join(
        f"- declaration {index}: `[{', '.join(names)}]`"
        for index, names in enumerate(axioms, start=1)
    )


def sealed_sources() -> tuple[bytes, bytes]:
    source = SOURCE.read_bytes()
    audit = AUDIT_SOURCE.read_bytes()
    for path, content in ((SOURCE, source), (AUDIT_SOURCE, audit)):
        measured = sha256(content)
        if measured != RAW_HASHES[path]:
            raise SystemExit(f"RAW_SOURCE_DRIFT={path.relative_to(ROOT)}/{measured}")
    if source.count(SOURCE_PRE) != 1 or audit.count(AUDIT_PRE) != 1:
        raise SystemExit("PRE_VALIDATION_BLOCK_SCOPE_MISMATCH")
    sealed_source = source.replace(SOURCE_PRE, b"")
    sealed_audit = audit.replace(AUDIT_PRE, b"")
    for path, content in ((SOURCE, sealed_source), (AUDIT_SOURCE, sealed_audit)):
        measured = sha256(content)
        if measured != SEALED_HASHES[path]:
            raise SystemExit(f"SEALED_SOURCE_HASH_MISMATCH={path.relative_to(ROOT)}/{measured}")
        if b"PRE-VALIDATION" in content:
            raise SystemExit(f"PRE_VALIDATION_SURVIVES={path.relative_to(ROOT)}")
    return sealed_source, sealed_audit


def map_section(result: dict[str, object]) -> bytes:
    focal = stage(result, "cmp99_finite_grid_aliasing_focal")
    audit = stage(result, "cmp99_finite_grid_aliasing_audit")
    text = f"""### Step 8b.22: exact finite-grid Fourier aliasing substrate (SEALED; cold run {RUN_ID}; 20/41 unchanged)

`BalabanCMP99FlatFiniteGridAliasing` starts item 3 of the finite post-Gate-7
route without identifying a finite DFT with an integral.  It reduces integer
Fourier frequencies into the exact multidimensional `ZMod` box, proves the
normalized character selector for an arbitrary residue class, and uses
absolute summability to exchange the finite grid sum with the infinite
Fourier series.  The endpoint is the literal sum of continuous coefficients
in that residue class.

Cold GitHub Actions run [{RUN_ID}]({RUN_URL}), job `{JOB_ID}`, validated exact
source `{result['source_sha']}` under workflow HEAD `{result['workflow_sha']}`.
The focal exited `{focal['exit']}` after `{focal['seconds']} s` with literal
`Build completed successfully ({result['focal_jobs']} jobs).`; the audit
exited `{audit['exit']}` after `{audit['seconds']} s`.  All seven measured
axiom blocks are recorded in ledger Addendum 867 and are subsets of
`{{propext, Classical.choice, Quot.sound}}`.  `FINAL_STATUS=PASS` and the
independent artifact audit verified `{result['manifest_entries']}` manifest
entries, `{result['inner_members']}` inner members and
`{result['outer_members']}` outer members.

The physical Fourier-series expansion of the CMP89 endpoint integrand is not
accepted as a premise or asserted here; it remains the next source-specific
producer.  This seal covers generic finite-grid aliasing only.  Regional
`B0`, window 15, terminal fields and a `TermSource` inhabitant remain open.
Counters stay exactly `20/41`, `TermSource = 0`; window 15 remains compatible
but unattained.
"""
    return text.encode()


def ledger_addendum(result: dict[str, object]) -> bytes:
    focal = stage(result, "cmp99_finite_grid_aliasing_focal")
    audit = stage(result, "cmp99_finite_grid_aliasing_audit")
    text = f"""

## Addendum 867 (2026-08-17, **finite-grid Fourier aliasing substrate sealed in cold GitHub Actions checkout; 20/41 unchanged**)

Cold run [{RUN_ID}]({RUN_URL}), job `{JOB_ID}`, checked exact source
`{result['source_sha']}` at workflow HEAD `{result['workflow_sha']}` with no
restored `.lake/build`.  The focal exited `{focal['exit']}` after
`{focal['seconds']} s` with the literal terminal line
`Build completed successfully ({result['focal_jobs']} jobs).`; the audit
exited `{audit['exit']}` after `{audit['seconds']} s`.

The seven measured axiom sets were:

{axiom_lines(result)}

The evidence-manifest SHA-256 is
`{result['evidence_manifest_sha256']}`; deterministic inner archive SHA-256 is
`{result['inner_archive_sha256']}`; raw GitHub artifact ZIP SHA-256 is
`{result['outer_artifact_zip_sha256']}`.  The independent validator checked
`{result['manifest_entries']}` manifest entries, `{result['inner_members']}`
inner members and `{result['outer_members']}` outer members, with literal
`FINAL_STATUS=PASS`.

This seal removes exactly the source and audit PRE-VALIDATION marks and adds
the audit to `YangMillsCore.lean`.  It proves generic finite-grid aliasing
only; it does not construct the physical Fourier-series expansion, regional
`B0`, attain window 15, discharge a terminal field or inhabit `TermSource`.
Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.
"""
    return text.encode()


def seal_plan(result: dict[str, object]) -> list[tuple[Path, bytes]]:
    if result.get("source_sha") != AUDIT["SOURCE_SHA"]:
        raise SystemExit("VALIDATED_SOURCE_SHA_MISMATCH")
    if result.get("workflow_sha") != AUDIT["WORKFLOW_SHA"]:
        raise SystemExit("VALIDATED_WORKFLOW_SHA_MISMATCH")
    source, audit_source = sealed_sources()

    core = CORE.read_bytes()
    if core.count(CORE_ANCHOR) != 1 or CORE_IMPORT in core:
        raise SystemExit("CORE_IMPORT_STATE_MISMATCH")
    core = core.replace(CORE_ANCHOR, CORE_ANCHOR + CORE_IMPORT)

    vertical = MAP.read_bytes()
    if vertical.count(MAP_HEADER) != 1:
        raise SystemExit("VERTICAL_MAP_STEP8B22_STATE_MISMATCH")
    position = vertical.index(MAP_HEADER)
    if vertical.find(b"\n### ", position + len(MAP_HEADER)) != -1:
        raise SystemExit("VERTICAL_MAP_STEP8B22_NOT_TERMINAL_SECTION")
    vertical = vertical[:position] + map_section(result)

    ledger = LEDGER.read_bytes()
    if b"## Addendum 867 " in ledger or b"## Addendum 866 " not in ledger:
        raise SystemExit("LEDGER_ADDENDUM_STATE_MISMATCH")
    ledger += ledger_addendum(result)

    return [
        (SOURCE, source),
        (AUDIT_SOURCE, audit_source),
        (CORE, core),
        (MAP, vertical),
        (LEDGER, ledger),
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--artifact-root", required=True, type=Path)
    parser.add_argument("--outer-zip", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    actual = git("rev-parse", "HEAD")
    if args.expected_head != EXPECTED_HEAD or actual != EXPECTED_HEAD:
        raise SystemExit(f"HEAD_MISMATCH={actual}")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--cached", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("INDEX_NOT_CLEAN")

    result = AUDIT["validate"](args.artifact_root, args.outer_zip)
    plan = seal_plan(result)
    if not args.write:
        print(
            "STEP8B22_SEAL_PREVIEW_OK "
            f"head={actual} run_id={RUN_ID} files={len(plan)} "
            f"focal_jobs={result['focal_jobs']}"
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
        "STEP8B22_SEAL_WRITE_OK "
        f"base_head={actual} run_id={RUN_ID} files={len(plan)}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"STEP8B22_SEAL_FAIL: {error}")
        raise SystemExit(1)
