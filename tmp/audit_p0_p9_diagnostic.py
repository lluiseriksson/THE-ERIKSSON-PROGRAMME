#!/usr/bin/env python3
"""Read-only static gate for the exact P0--P9 scratch diagnostic.

This binds all shipped bytes and checks P9's semantic boundary.  It is not a
Lean elaboration and must never be reported as compiler evidence.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
PATHS = ROOT / "tmp/P0-P9-SCRATCH-PATHS.txt"
MANIFEST = ROOT / "tmp/P0-P9-SCRATCH-MANIFEST.sha256"
EXPECTED_PATHS_SHA256 = (
    "FEC594C0FBA52E14F8CC1E1BA886202FCDF2E425DE2C93E56DBF59FEEBB2FA61"
)
EXPECTED_MANIFEST_SHA256 = (
    "49C08AE0FD0FA1B496183FF8F4386EB44DAEDB673BEAC16779031E8AFA921395"
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(
    r"(?m)^#print axioms (?:YangMills\.RG\.)?([A-Za-z0-9_.'’]+)"
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def fail(message: str) -> None:
    raise SystemExit(message)


def main() -> int:
    baseline = subprocess.run(
        [sys.executable, str(ROOT / "tmp/audit_p0_p8_diagnostic.py")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if baseline.returncode != 0:
        fail("P0_P8_BASELINE_FAILED=" + (baseline.stdout + baseline.stderr).strip())

    if digest(PATHS) != EXPECTED_PATHS_SHA256:
        fail(f"P0_P9_PATH_LIST_DRIFT={digest(PATHS)}")
    if digest(MANIFEST) != EXPECTED_MANIFEST_SHA256:
        fail(f"P0_P9_MANIFEST_DRIFT={digest(MANIFEST)}")

    paths = [line for line in PATHS.read_text(encoding="utf-8-sig").splitlines() if line]
    rows: list[tuple[str, str]] = []
    for number, line in enumerate(
        MANIFEST.read_text(encoding="utf-8-sig").splitlines(), start=1
    ):
        match = re.fullmatch(r"([0-9A-Fa-f]{64})\s+(.+)", line)
        if match is None:
            fail(f"P0_P9_BAD_MANIFEST_ROW={number}")
        rows.append((match.group(1).upper(), match.group(2)))
    if len(paths) != 39 or len(rows) != 39:
        fail(f"P0_P9_SCOPE_COUNT={len(paths)}/{len(rows)}")
    if [path for _, path in rows] != paths:
        fail("P0_P9_PATH_MANIFEST_ORDER_MISMATCH")
    for expected, relative in rows:
        measured = digest(ROOT / relative)
        if measured != expected:
            fail(f"P0_P9_BLOB_DRIFT={relative}/{measured}")
        text = (ROOT / relative).read_text(encoding="utf-8-sig")
        if re.search(
            r"(?s)/--.*?-/\s*set_option\s+[^\n]+\s+in\s*\n\s*(?:theorem|lemma)",
            text,
        ):
            fail(f"P0_P9_DOCSTRING_BEFORE_SCOPED_OPTION={relative}")

    source_path = ROOT / "tmp/P9SourceSeparatedPrefixCombesThomas.lean"
    audit_path = ROOT / "tmp/P9SourceSeparatedPrefixCombesThomasAudit.lean"
    source = source_path.read_text(encoding="utf-8-sig")
    audit = audit_path.read_text(encoding="utf-8-sig")
    declarations = DECL.findall(source)
    prints = PRINT.findall(audit)
    if len(declarations) != 12 or prints != declarations:
        fail(f"P9_AUDIT_SCOPE_MISMATCH={len(declarations)}/{len(prints)}")
    if audit.splitlines()[0] != "import tmp.P9SourceSeparatedPrefixCombesThomas":
        fail("P9_AUDIT_IMPORT_MISMATCH")
    for token in ("sorry", "admit", "by?", "exact?"):
        if token in source or token in audit:
            fail(f"P9_FORBIDDEN_PLACEHOLDER={token}")
    for forbidden in (
        "cmp99SourceGeneratedPhysicalMass",
        "cmp99SourceGeneratedPhysicalPrecision hd",
        "window 15 is attained",
        "uniform in depth",
    ):
        if forbidden in source:
            fail(f"P9_WRONG_SEMANTIC_SUBSTITUTION={forbidden}")
    for required in (
        "scratch_cmp85SourcePrefixCountingCoefficient",
        "cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower",
        "cmp99SourceIteratedLift_QprimeMass_finiteRange",
        "finitePiLpExponentialKernelBound_of_coercive",
        "finitePiLpTypedExponentialKernelBound_reindex",
        "cmp99RegionalDirichletGreen_exponentialKernelBound",
        "per-depth statement only",
        "does not produce uniform CMP99 (3.42) constants",
    ):
        if required not in source:
            fail(f"P9_REQUIRED_BOUNDARY_MISSING={required}")

    print(
        "P0_P9_DIAGNOSTIC_STATIC_OK "
        "files=39 p9_declarations=12 compiler_verified=false "
        f"manifest_sha256={EXPECTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
