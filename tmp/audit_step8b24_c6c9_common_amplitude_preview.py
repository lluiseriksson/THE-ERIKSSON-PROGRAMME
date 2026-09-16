#!/usr/bin/env python3
"""Fail-closed promotion preview for the C6c.9 common amplitude pair."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
SOURCE = TMP / "BalabanCMP99Eq342CommonAmplitude.draft.lean"
AUDIT = TMP / "BalabanCMP99Eq342CommonAmplitudeAudit.draft.lean"
TARGET_SOURCE = ROOT / "YangMills/RG/BalabanCMP99Eq342CommonAmplitude.lean"
TARGET_AUDIT = ROOT / "YangMills/RG/BalabanCMP99Eq342CommonAmplitudeAudit.lean"
SOURCE_SHA256 = "4A380139EB1A290C1840A09C3C69AC5A939C6E0985E46565D24833D458F13FA6"
AUDIT_SHA256 = "9DC5B31AD39AAB31D9A1936DAEBD81EB238D80407A1FA19978FA3DF1947F039B"
RAW_NAMES = (
    "cmp99Eq342CommonAmplitude_draft",
    "cmp99Eq342CommonAmplitude_pos_draft",
    "le_cmp99Eq342CommonAmplitude_value_draft",
    "le_cmp99Eq342CommonAmplitude_left_draft",
    "le_cmp99Eq342CommonAmplitude_right_draft",
    "le_cmp99Eq342CommonAmplitude_laplacian_draft",
)
FINAL_NAMES = tuple(name.removesuffix("_draft") for name in RAW_NAMES)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def read_pinned(path: Path, expected: str) -> str:
    if not path.is_file():
        raise SystemExit(f"C6C9_COMMON_RAW_MISSING={path.relative_to(ROOT)}")
    data = path.read_bytes()
    actual = sha256(data)
    if actual != expected:
        raise SystemExit(f"C6C9_COMMON_RAW_HASH_MISMATCH={path.name}/{actual}")
    return data.decode("utf-8")


def promote_source(text: str) -> bytes:
    if text.count("PRE-VALIDATION:") != 1:
        raise SystemExit("C6C9_COMMON_SOURCE_PRE_VALIDATION_COUNT")
    declarations = tuple(re.findall(
        r"(?m)^(?:def|theorem)\s+([A-Za-z0-9_']+)", text
    ))
    if declarations != RAW_NAMES:
        raise SystemExit("C6C9_COMMON_SOURCE_DECLARATION_SCOPE=" + repr(declarations))
    required = (
        "1 + Avalue + Aleft + Aright + Alaplacian",
        "hvalue : 0 ≤ Avalue",
        "hleft : 0 ≤ Aleft",
        "hright : 0 ≤ Aright",
        "hlaplacian : 0 ≤ Alaplacian",
    )
    missing = [token for token in required if token not in text]
    if missing:
        raise SystemExit("C6C9_COMMON_SEMANTIC_TOKEN_MISSING=" + repr(missing))
    promoted = text.replace("_draft", "")
    promoted_declarations = tuple(re.findall(
        r"(?m)^(?:def|theorem)\s+([A-Za-z0-9_']+)", promoted
    ))
    if promoted_declarations != FINAL_NAMES:
        raise SystemExit("C6C9_COMMON_PROMOTED_DECLARATION_SCOPE")
    return promoted.replace("\r\n", "\n").encode("utf-8")


def promote_audit(text: str) -> bytes:
    if text.count("PRE-VALIDATION audit:") != 1:
        raise SystemExit("C6C9_COMMON_AUDIT_PRE_VALIDATION_COUNT")
    expected_import = "import YangMills.RG.BalabanCMP99Eq342CommonAmplitude"
    if text.count(expected_import) != 1:
        raise SystemExit("C6C9_COMMON_AUDIT_IMPORT_SCOPE")
    readouts = tuple(
        name.rsplit(".", 1)[-1]
        for name in re.findall(r"(?m)^#print axioms\s+([^\s]+)\s*$", text)
    )
    if readouts != FINAL_NAMES:
        raise SystemExit("C6C9_COMMON_AUDIT_READOUT_SCOPE=" + repr(readouts))
    return text.replace("\r\n", "\n").encode("utf-8")


def promotion_rows() -> tuple[tuple[Path, bytes], ...]:
    present = [
        path.relative_to(ROOT).as_posix()
        for path in (TARGET_SOURCE, TARGET_AUDIT) if path.exists()
    ]
    if present:
        raise SystemExit("C6C9_COMMON_TARGET_EXISTS=" + ",".join(present))
    return (
        (TARGET_SOURCE, promote_source(read_pinned(SOURCE, SOURCE_SHA256))),
        (TARGET_AUDIT, promote_audit(read_pinned(AUDIT, AUDIT_SHA256))),
    )


def manifest_digest(rows: tuple[tuple[Path, bytes], ...]) -> str:
    payload = "".join(
        f"{hashlib.sha256(data).hexdigest()}  {path.relative_to(ROOT).as_posix()}\n"
        for path, data in rows
    ).encode("utf-8")
    return sha256(payload)


def main() -> int:
    rows = promotion_rows()
    print(
        "STEP8B24_C6C9_COMMON_AMPLITUDE_PREVIEW_OK "
        "files=2 declarations=6 audit_readouts=6 "
        f"manifest_sha256={manifest_digest(rows)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

