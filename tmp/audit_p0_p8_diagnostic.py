#!/usr/bin/env python3
"""Read-only static gate for the P0--P5/P7/P8 diagnostic closure.

This is not a Lean elaboration check.  It binds the exact scratch bytes and
fails closed on the semantic substitutions that would make the new regional
Green a different object from the source-faithful CMP85/P5 chain.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
PATHS = ROOT / "tmp/P0-P8-SCRATCH-PATHS.txt"
MANIFEST = ROOT / "tmp/P0-P8-SCRATCH-MANIFEST.sha256"
EXPECTED_PATHS_SHA256 = (
    "4729A2680F020CFDEF9BE8AC08BE120462A3A59DAD2D892BBC14139CCB55C049"
)
EXPECTED_MANIFEST_SHA256 = (
    "1CFEB5CADBB0D36AC212EDD4D7F44799DD4E5BA49A47E6A30F31E349C2F0A9E3"
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def fail(message: str) -> None:
    raise SystemExit(message)


def main() -> int:
    if digest(PATHS) != EXPECTED_PATHS_SHA256:
        fail(f"P0_P8_PATH_LIST_DRIFT={digest(PATHS)}")
    if digest(MANIFEST) != EXPECTED_MANIFEST_SHA256:
        fail(f"P0_P8_MANIFEST_DRIFT={digest(MANIFEST)}")

    paths = [line for line in PATHS.read_text(encoding="utf-8-sig").splitlines() if line]
    rows: list[tuple[str, str]] = []
    for number, line in enumerate(
        MANIFEST.read_text(encoding="utf-8-sig").splitlines(), start=1
    ):
        match = re.fullmatch(r"([0-9A-Fa-f]{64})\s+(.+)", line)
        if match is None:
            fail(f"P0_P8_BAD_MANIFEST_ROW={number}")
        rows.append((match.group(1).upper(), match.group(2)))
    if len(paths) != 37 or len(rows) != 37:
        fail(f"P0_P8_SCOPE_COUNT={len(paths)}/{len(rows)}")
    if [path for _, path in rows] != paths:
        fail("P0_P8_PATH_MANIFEST_ORDER_MISMATCH")
    for expected, relative in rows:
        measured = digest(ROOT / relative)
        if measured != expected:
            fail(f"P0_P8_BLOB_DRIFT={relative}/{measured}")

    pairs = (
        (
            "tmp/P7SourceSeparatedAmbientPrefixPrecision.lean",
            "tmp/P7SourceSeparatedAmbientPrefixPrecisionAudit.lean",
            8,
        ),
        (
            "tmp/P8SourceSeparatedRegionalPrefixGreen.lean",
            "tmp/P8SourceSeparatedRegionalPrefixGreenAudit.lean",
            5,
        ),
    )
    for source_path, audit_path, count in pairs:
        source = (ROOT / source_path).read_text(encoding="utf-8-sig")
        audit = (ROOT / audit_path).read_text(encoding="utf-8-sig")
        declarations = DECL.findall(source)
        prints = PRINT.findall(audit)
        if len(declarations) != count or prints != declarations:
            fail(
                "P0_P8_AUDIT_SCOPE_MISMATCH="
                f"{source_path}/{len(declarations)}/{len(prints)}"
            )
        expected_import = "import tmp." + Path(source_path).stem
        if audit.splitlines()[0] != expected_import:
            fail(f"P0_P8_AUDIT_IMPORT_MISMATCH={audit_path}")
        for token in ("sorry", "admit", "by?", "exact?"):
            if token in source or token in audit:
                fail(f"P0_P8_FORBIDDEN_PLACEHOLDER={source_path}/{token}")

    p7 = (ROOT / pairs[0][0]).read_text(encoding="utf-8-sig")
    p8 = (ROOT / pairs[1][0]).read_text(encoding="utf-8-sig")
    if "cmp99SourceGeneratedPhysicalMass" in p7 + p8:
        fail("P0_P8_WRONG_GENERATED_MASS_SURVIVES")
    for required in (
        "scratch_cmp85LastPositivePrefix_succ_sourceIndex",
        "scratch_cmp89SourceSeparatedFinePrefixPrecision",
        "scratch_cmp89SourceSeparatedAmbientPrefixGreen",
        "scratch_cmp89SourceSeparatedAmbientPrefixPrecision_comp_green",
        "scratch_cmp89SourceSeparatedAmbientPrefixGreen_comp_precision",
    ):
        if required not in p7:
            fail(f"P7_REQUIRED_OBJECT_MISSING={required}")
    for required in (
        "cmp99SourceSeparatedLargeBlockSquarePartition",
        "(L ^ (depth + 1))",
        "scratch_cmp89SourceSeparatedAmbientPrefixPrecision",
        "cmp99RegionalDirichletGreen",
        "cmp99RegionalDirichletPrecision_comp_green",
    ):
        if required not in p8:
            fail(f"P8_REQUIRED_OBJECT_MISSING={required}")

    print(
        "P0_P8_DIAGNOSTIC_STATIC_OK "
        "files=37 p7_declarations=8 p8_declarations=5 "
        f"manifest_sha256={EXPECTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
