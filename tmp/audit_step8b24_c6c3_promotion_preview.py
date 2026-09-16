#!/usr/bin/env python3
"""Read-only, fail-closed promotion preview for the C6c.3 source/audit pair.

The preview does not write tracked files and does not invoke Lean.  It freezes
the exact two scratch blobs, their future tracked paths, the source-sign
dictionary, the inverse-square budget, and the audit readout scope.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
SOURCE = TMP / "BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacian.lean"
AUDIT = TMP / "BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacianAudit.lean"
TARGET_SOURCE = ROOT / "YangMills/RG/BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacian.lean"
TARGET_AUDIT = ROOT / "YangMills/RG/BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacianAudit.lean"
EXTERNAL_SOURCE = (
    ROOT / "YangMills/RG/BalabanCMP99SourceSeparatedSignedCutoffLaplacian.lean"
)

EXPECTED_RAW = {
    SOURCE: "4A1B92B8D55AB28C47F9EAE483CF46B8FF09A6CF892BD8887956F1BEFD41A52D",
    AUDIT: "A7D9438FAD9D637B6C56D7492EA2231A7883A6F71C149D5B6CEB58DF79650805",
}

SOURCE_IMPORT = (
    "import YangMills.RG."
    "BalabanCMP99SourceSeparatedSignedCutoffLaplacian"
)
AUDIT_IMPORT = (
    "import YangMills.RG."
    "BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacian"
)
THEOREMS = (
    "cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm_eq_neg_correction",
    "norm_cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm_le",
    "cmp96Eq240SourceSeparatedSignedCutoffLaplacianBudget_mul_range_sq",
)
DEFINITION = "cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def read_exact(path: Path) -> bytes:
    if not path.is_file():
        raise SystemExit(f"C6C3_RAW_MISSING={path.relative_to(ROOT)}")
    data = path.read_bytes()
    measured = sha256(data)
    expected = EXPECTED_RAW[path]
    if measured != expected:
        raise SystemExit(
            f"C6C3_RAW_HASH_MISMATCH={path.relative_to(ROOT)}/{measured}"
        )
    return data


def declarations(text: str) -> tuple[str, ...]:
    return tuple(
        re.findall(
            r"(?m)^\s*(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z0-9_']+)",
            text,
        )
    )


def audit_readouts(text: str) -> tuple[str, ...]:
    return tuple(
        name.rsplit(".", 1)[-1]
        for name in re.findall(r"(?m)^#print axioms\s+([A-Za-z0-9_'.]+)\s*$", text)
    )


def verify_source(text: str) -> None:
    if not EXTERNAL_SOURCE.is_file():
        raise SystemExit("C6C3_SOURCE_IMPORT_UNRESOLVED")
    if text.count("PRE-VALIDATION:") != 1:
        raise SystemExit("C6C3_SOURCE_PRE_VALIDATION_COUNT")
    if text.count(SOURCE_IMPORT) != 1:
        raise SystemExit("C6C3_SOURCE_IMPORT_SCOPE")
    if "BalabanCMP96Eq240SourceSeparatedCutoffLaplacian\n" in text:
        raise SystemExit("C6C3_SOURCE_IMPORTS_REJECTED_FIRST_DIFFERENCE_MODULE")
    if "tmp." in text or "scratch_" in text or "Scratch" in text:
        raise SystemExit("C6C3_SOURCE_PROVISIONAL_TOKEN")
    expected_declarations = (DEFINITION, *THEOREMS)
    measured_declarations = declarations(text)
    if measured_declarations != expected_declarations:
        raise SystemExit(
            "C6C3_SOURCE_DECLARATION_SCOPE=" + ",".join(measured_declarations)
        )

    required = (
        "-(cmp99SourceSeparatedSignedCutoffLaplacianCoefficient",
        "-cmp99CutoffLaplacianCorrection",
        "cmp99CutoffLaplacianCorrection_one_eq_sourceSeparatedSignedCoefficient",
        "(48 * P.secondDerivBound) /",
        "cmp99SourceSeparatedLargeBlockCutoffScale L K depth ^ 2",
        "(12 * P.secondDerivBound) / (K : ℝ) ^ 2",
        "cmp99SourceSeparatedSignedCutoffLaplacianBudget_mul_range_sq",
    )
    missing = [token for token in required if token not in text]
    if missing:
        raise SystemExit("C6C3_SOURCE_SEMANTIC_TOKEN_MISSING=" + repr(missing))
    forbidden_claims = ("window 15 attained", "TermSource")
    if any(token in text for token in forbidden_claims):
        raise SystemExit("C6C3_SOURCE_SCOPE_OVERCLAIM")


def verify_audit(text: str) -> None:
    if text.count("PRE-VALIDATION:") != 1:
        raise SystemExit("C6C3_AUDIT_PRE_VALIDATION_COUNT")
    if text.count(AUDIT_IMPORT) != 1:
        raise SystemExit("C6C3_AUDIT_IMPORT_SCOPE")
    if audit_readouts(text) != (DEFINITION, *THEOREMS):
        raise SystemExit(
            "C6C3_AUDIT_READOUT_SCOPE=" + ",".join(audit_readouts(text))
        )


def promotion_rows() -> tuple[tuple[Path, bytes], ...]:
    if TARGET_SOURCE.exists() or TARGET_AUDIT.exists():
        present = [
            path.relative_to(ROOT).as_posix()
            for path in (TARGET_SOURCE, TARGET_AUDIT)
            if path.exists()
        ]
        raise SystemExit("C6C3_PROMOTION_TARGET_EXISTS=" + ",".join(present))
    source = read_exact(SOURCE)
    audit = read_exact(AUDIT)
    verify_source(source.decode("utf-8"))
    verify_audit(audit.decode("utf-8"))
    return ((TARGET_SOURCE, source), (TARGET_AUDIT, audit))


def manifest_digest(rows: tuple[tuple[Path, bytes], ...]) -> str:
    manifest = "".join(
        f"{hashlib.sha256(data).hexdigest()}  {path.relative_to(ROOT).as_posix()}\n"
        for path, data in rows
    ).encode("utf-8")
    return sha256(manifest)


def main() -> int:
    rows = promotion_rows()
    print(
        "STEP8B24_C6C3_PROMOTION_PREVIEW_OK "
        f"files={len(rows)} declarations={1 + len(THEOREMS)} "
        f"audit_readouts={1 + len(THEOREMS)} "
        f"manifest_sha256={manifest_digest(rows)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
