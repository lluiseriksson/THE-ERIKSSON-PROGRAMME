#!/usr/bin/env python3
"""Fail-closed promotion preview for the C6c.9 weakening lemma.

This script is static instrumentation only.  It pins the two scratch inputs,
checks exact declaration/readout coverage and produces the future promoted
bytes in memory without writing the tracked tree.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
SOURCE = TMP / "FinitePiLpBlockLocalizedSupMonotone.draft.lean"
AUDIT = TMP / "FinitePiLpBlockLocalizedSupMonotoneAudit.draft.lean"
TARGET_SOURCE = ROOT / "YangMills/RG/FinitePiLpBlockLocalizedSupMonotone.lean"
TARGET_AUDIT = ROOT / "YangMills/RG/FinitePiLpBlockLocalizedSupMonotoneAudit.lean"
PREREQUISITE = ROOT / "YangMills/RG/FinitePiLpBlockLocalizedSup.lean"
SOURCE_SHA256 = "40F0A4F67F62256D360561619A4B9FC4E68293D621512486550C63A116A9DA29"
AUDIT_SHA256 = "A94C9A9F50922F2CDC4DFF6C790C11687A46C3BFEBA3EADE66F06E53B77702F0"
SOURCE_NAME = "finitePiLpTypedBlockLocalizedSupBound_mono_draft"
TARGET_NAME = "finitePiLpTypedBlockLocalizedSupBound_mono"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def read_pinned(path: Path, expected: str) -> str:
    if not path.is_file():
        raise SystemExit(f"C6C9_WEAKENING_RAW_MISSING={path.relative_to(ROOT)}")
    data = path.read_bytes()
    actual = sha256(data)
    if actual != expected:
        raise SystemExit(
            f"C6C9_WEAKENING_RAW_HASH_MISMATCH={path.relative_to(ROOT)}/{actual}"
        )
    return data.decode("utf-8")


def promote_source(text: str) -> bytes:
    if not PREREQUISITE.is_file():
        raise SystemExit("C6C9_WEAKENING_PREREQUISITE_MISSING")
    if text.count("PRE-VALIDATION:") != 1:
        raise SystemExit("C6C9_WEAKENING_SOURCE_PRE_VALIDATION_COUNT")
    if text.count("import YangMills.RG.FinitePiLpBlockLocalizedSup") != 1:
        raise SystemExit("C6C9_WEAKENING_SOURCE_IMPORT_SCOPE")
    declarations = re.findall(
        r"(?m)^theorem\s+([A-Za-z0-9_']+)", text
    )
    if declarations != [SOURCE_NAME]:
        raise SystemExit("C6C9_WEAKENING_SOURCE_DECLARATION_SCOPE=" + repr(declarations))
    for token in ("sorry", "admit", "axiom "):
        if re.search(rf"(?m)^.*\b{re.escape(token.strip())}\b", text):
            raise SystemExit("C6C9_WEAKENING_SOURCE_FORBIDDEN=" + token.strip())
    required = (
        "hA : A ≤ A'",
        "hrate : 0 < rate",
        "hrate_decay : rate ≤ decay",
        "Real.exp_le_exp.mpr",
        "finitePiLpSupNorm_nonneg f",
    )
    missing = [token for token in required if token not in text]
    if missing:
        raise SystemExit("C6C9_WEAKENING_SEMANTIC_TOKEN_MISSING=" + repr(missing))
    promoted = text.replace(SOURCE_NAME, TARGET_NAME)
    if SOURCE_NAME in promoted or promoted.count(TARGET_NAME) != 1:
        raise SystemExit("C6C9_WEAKENING_SOURCE_RENAME_SCOPE")
    return promoted.replace("\r\n", "\n").encode("utf-8")


def promote_audit(text: str) -> bytes:
    if text.count("PRE-VALIDATION audit:") != 1:
        raise SystemExit("C6C9_WEAKENING_AUDIT_PRE_VALIDATION_COUNT")
    expected_import = "import YangMills.RG.FinitePiLpBlockLocalizedSupMonotone"
    if text.count(expected_import) != 1:
        raise SystemExit("C6C9_WEAKENING_AUDIT_IMPORT_SCOPE")
    readouts = re.findall(r"(?m)^#print axioms\s+([^\s]+)\s*$", text)
    expected = ["YangMills.RG." + TARGET_NAME]
    if readouts != expected:
        raise SystemExit("C6C9_WEAKENING_AUDIT_READOUT_SCOPE=" + repr(readouts))
    return text.replace("\r\n", "\n").encode("utf-8")


def promotion_rows() -> tuple[tuple[Path, bytes], ...]:
    present = [
        path.relative_to(ROOT).as_posix()
        for path in (TARGET_SOURCE, TARGET_AUDIT)
        if path.exists()
    ]
    if present:
        raise SystemExit("C6C9_WEAKENING_TARGET_EXISTS=" + ",".join(present))
    source = promote_source(read_pinned(SOURCE, SOURCE_SHA256))
    audit = promote_audit(read_pinned(AUDIT, AUDIT_SHA256))
    return ((TARGET_SOURCE, source), (TARGET_AUDIT, audit))


def manifest_digest(rows: tuple[tuple[Path, bytes], ...]) -> str:
    payload = "".join(
        f"{hashlib.sha256(data).hexdigest()}  {path.relative_to(ROOT).as_posix()}\n"
        for path, data in rows
    ).encode("utf-8")
    return sha256(payload)


def main() -> int:
    rows = promotion_rows()
    print(
        "STEP8B24_C6C9_WEAKENING_PREVIEW_OK "
        "files=2 declarations=1 audit_readouts=1 "
        f"manifest_sha256={manifest_digest(rows)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

