#!/usr/bin/env python3
"""Fail-closed static promotion preview for C6c.8 f2g through f5b.

This instrumentation never writes the tracked tree.  It pins the complete
forty-file scratch closure, checks target collisions and the new f5b public
surface, and computes the bytes that a later promotion would materialize.
It is not a Lean, Lake or axiom-oracle verdict.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PATH_LIST = ROOT / "tmp" / "C6C8F5B-FULL-SCRATCH-PATHS.txt"
PATH_LIST_SHA256 = "BC82023D89DB02FE398748944D5BB7DE28722EC157846AAC5BA76FC52F2E1277"
RAW_AGGREGATE_SHA256 = "15480683C94A3E6AF095DA53B3AD1EC197E444FE706C95ADD3DA38E0882E7008"
PROMOTED_MANIFEST_SHA256 = "7BB90E48BB18EBFE8777F24D5CBEBA71E3B1B980B7E6AAD137207F73E35D1B29"

NEW_SOURCE = (
    ROOT / "tmp" /
    "BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.draft.lean"
)
NEW_AUDIT = (
    ROOT / "tmp" /
    "BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.draft.lean"
)
NEW_SOURCE_SHA256 = "766A608169D73E3A95FB433A672AA4B480F5794BF896310283BC9D22D3F9D589"
NEW_AUDIT_SHA256 = "3A43F4DB35A374160B9AADF37913CF29B1E9547DC1B9A94FA10D25DCAF40BD0D"

EXPECTED_NEW = (
    "CMP99Eq335PhysicalRegularityWitness.localizedRetainedTowerOfSourceRegion",
    "CMP99Eq335PhysicalRegularityWitness."
    "localizedRetainedTerminalQprime_eq_ofSourceRegion",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def target_for(relative: str) -> Path:
    name = Path(relative).name
    if not name.endswith(".draft.lean"):
        raise SystemExit(f"C6C8F5B_BAD_SCRATCH_SUFFIX={relative}")
    return ROOT / "YangMills" / "RG" / name.replace(".draft.lean", ".lean")


def read_paths() -> list[str]:
    if not PATH_LIST.is_file():
        raise SystemExit("C6C8F5B_PATH_LIST_MISSING")
    if sha256(PATH_LIST.read_bytes()) != PATH_LIST_SHA256:
        raise SystemExit("C6C8F5B_PATH_LIST_HASH_MISMATCH")
    paths = [
        line.strip()
        for line in PATH_LIST.read_text(encoding="utf-8-sig").splitlines()
        if line.strip()
    ]
    if len(paths) != 40 or len(set(paths)) != 40:
        raise SystemExit(f"C6C8F5B_PATH_SCOPE={len(paths)}/{len(set(paths))}")
    if any(not path.startswith("tmp/") for path in paths):
        raise SystemExit("C6C8F5B_PATH_OUTSIDE_TMP")
    return paths


def read_closure(paths: list[str]) -> list[tuple[str, bytes]]:
    rows: list[tuple[str, bytes]] = []
    raw_lines: list[str] = []
    for relative in paths:
        path = ROOT / relative
        if not path.is_file():
            raise SystemExit(f"C6C8F5B_RAW_MISSING={relative}")
        data = path.read_bytes()
        raw_lines.append(f"{sha256(data)}  {relative}\n")
        text = data.decode("utf-8-sig")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"C6C8F5B_PREVALIDATION_COUNT={relative}")
        if re.search(r"(?m)^\s*(?:sorry|admit|axiom)\b", text):
            raise SystemExit(f"C6C8F5B_FORBIDDEN_DECLARATION={relative}")
        target = target_for(relative)
        if target.exists():
            raise SystemExit(
                "C6C8F5B_TARGET_EXISTS=" + target.relative_to(ROOT).as_posix()
            )
        rows.append((target.relative_to(ROOT).as_posix(), data.replace(b"\r\n", b"\n")))
    if sha256("".join(raw_lines).encode()) != RAW_AGGREGATE_SHA256:
        raise SystemExit("C6C8F5B_RAW_AGGREGATE_HASH_MISMATCH")
    return rows


def check_new_surface() -> None:
    if sha256(NEW_SOURCE.read_bytes()) != NEW_SOURCE_SHA256:
        raise SystemExit("C6C8F5B_NEW_SOURCE_HASH_MISMATCH")
    if sha256(NEW_AUDIT.read_bytes()) != NEW_AUDIT_SHA256:
        raise SystemExit("C6C8F5B_NEW_AUDIT_HASH_MISMATCH")
    source = NEW_SOURCE.read_text(encoding="utf-8-sig")
    audit = NEW_AUDIT.read_text(encoding="utf-8-sig")
    declarations = [
        name for name in re.findall(
            r"(?m)^(?:noncomputable\s+)?(?:def|theorem)\s+"
            r"([A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*)",
            source,
        )
        if name.startswith("CMP99Eq335PhysicalRegularityWitness.")
    ]
    readouts = re.findall(
        r"(?m)^#print axioms YangMills\.RG\.([^\s]+)\s*$", audit
    )
    if tuple(declarations) != EXPECTED_NEW:
        raise SystemExit(f"C6C8F5B_DECLARATION_MISMATCH={declarations!r}")
    if tuple(readouts) != EXPECTED_NEW:
        raise SystemExit(f"C6C8F5B_AUDIT_READOUT_MISMATCH={readouts!r}")
    required = (
        "CMP99Eq335Corollary36SourceRegionDictionary",
        "retainedFineReadCarrierInsideRegularCube W.cube D regions",
        "W.localizedRetainedTower regions hM rho",
        "CMP99SourceLocalizedRetainedTower.terminalQprime_eq",
    )
    missing = [token for token in required if token not in source]
    if missing:
        raise SystemExit(f"C6C8F5B_REQUIRED_MECHANISM_MISSING={missing!r}")
    forbidden = (
        "(hinside :",
        "fineSmall :",
        "value_bound :",
        "left_derivative_bound :",
        "right_adjoint_derivative_bound :",
        "laplacian_bound :",
    )
    present = [token for token in forbidden if token in source]
    if present:
        raise SystemExit(f"C6C8F5B_FORBIDDEN_RENAMING_PRESENT={present!r}")


def manifest_digest(rows: list[tuple[str, bytes]]) -> str:
    payload = "".join(
        f"{sha256(data)}  {relative}\n" for relative, data in rows
    ).encode()
    return sha256(payload)


def main() -> int:
    paths = read_paths()
    rows = read_closure(paths)
    check_new_surface()
    actual_manifest = manifest_digest(rows)
    if actual_manifest != PROMOTED_MANIFEST_SHA256:
        raise SystemExit(
            f"C6C8F5B_PROMOTED_MANIFEST_MISMATCH={actual_manifest}"
        )
    print(
        "STEP8B24_C6C8F5B_PROMOTION_PREVIEW_OK "
        "files=40 new_declarations=2 new_audit_readouts=2 "
        f"manifest_sha256={actual_manifest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
