#!/usr/bin/env python3
"""Fail-closed static preview for the four-file CMP99 (3.35) class layer.

This script is read-only.  It pins the all-cubes class, the regional consumer
that eliminates a free one-cube witness, and both axiom audits.  It is not a
Lean, Lake or oracle verdict.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PATH_LIST = ROOT / "tmp" / "C6D-EQ335-REGULARITY-CLASS-CONSUMER-PATHS.txt"
PATH_LIST_SHA256 = "DC33A93BA9F006561A4BC934C034CC2F37B55D625E318C7FA781A098C5A76220"
RAW_AGGREGATE_SHA256 = "C39F3995D0310E391EABA06F2E36E143141FC92988E37E47E4EB11334F365E70"
PROMOTED_MANIFEST_SHA256 = "541381D7C8238DF851A372C0A84489FA96F5709418A8146BAF60811B15EA21AE"

EXPECTED = (
    "CMP99Eq335PhysicalCubeRegularityData",
    "CMP99Eq335PhysicalRegularityClass",
    "CMP99Eq335PhysicalRegularityClass.toCubeWitness",
    "CMP99Eq335PhysicalRegularityClass.localizedRetainedTowerOfSourceRegion",
    "CMP99Eq335PhysicalRegularityClass."
    "localizedRetainedTerminalQprime_eq_ofSourceRegion",
)

PREREQUISITE_TARGETS = (
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityWitness.lean",
    "YangMills/RG/"
    "BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.lean",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def target_for(relative: str) -> Path:
    name = Path(relative).name
    if not name.endswith(".draft.lean"):
        raise SystemExit(f"C6D_EQ335_BAD_SCRATCH_SUFFIX={relative}")
    return ROOT / "YangMills" / "RG" / name.replace(".draft.lean", ".lean")


def read_paths() -> list[str]:
    if not PATH_LIST.is_file():
        raise SystemExit("C6D_EQ335_PATH_LIST_MISSING")
    if sha256(PATH_LIST.read_bytes()) != PATH_LIST_SHA256:
        raise SystemExit("C6D_EQ335_PATH_LIST_HASH_MISMATCH")
    paths = [
        line.strip()
        for line in PATH_LIST.read_text(encoding="utf-8-sig").splitlines()
        if line.strip()
    ]
    if len(paths) != 4 or len(set(paths)) != 4:
        raise SystemExit(f"C6D_EQ335_PATH_SCOPE={len(paths)}/{len(set(paths))}")
    if any(not path.startswith("tmp/") for path in paths):
        raise SystemExit("C6D_EQ335_PATH_OUTSIDE_TMP")
    return paths


def read_layer(paths: list[str]) -> list[tuple[str, bytes]]:
    rows: list[tuple[str, bytes]] = []
    raw_lines: list[str] = []
    for relative in paths:
        path = ROOT / relative
        if not path.is_file():
            raise SystemExit(f"C6D_EQ335_RAW_MISSING={relative}")
        data = path.read_bytes()
        raw_lines.append(f"{sha256(data)}  {relative}\n")
        text = data.decode("utf-8-sig")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"C6D_EQ335_PREVALIDATION_COUNT={relative}")
        if re.search(r"(?m)^\s*(?:sorry|admit|axiom)\b", text):
            raise SystemExit(f"C6D_EQ335_FORBIDDEN_DECLARATION={relative}")
        target = target_for(relative)
        if target.exists():
            raise SystemExit(
                "C6D_EQ335_TARGET_EXISTS=" + target.relative_to(ROOT).as_posix()
            )
        rows.append((target.relative_to(ROOT).as_posix(), data.replace(b"\r\n", b"\n")))
    if sha256("".join(raw_lines).encode()) != RAW_AGGREGATE_SHA256:
        raise SystemExit("C6D_EQ335_RAW_AGGREGATE_HASH_MISMATCH")
    return rows


def check_surface(paths: list[str]) -> None:
    sources = [
        (ROOT / path).read_text(encoding="utf-8-sig")
        for path in paths
        if not path.endswith("Audit.draft.lean")
    ]
    audits = [
        (ROOT / path).read_text(encoding="utf-8-sig")
        for path in paths
        if path.endswith("Audit.draft.lean")
    ]
    declaration_pattern = re.compile(
        r"(?m)^(?:noncomputable\s+)?(?:structure|def|theorem)\s+"
        r"([A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*)"
    )
    declarations = [name for text in sources for name in declaration_pattern.findall(text)]
    readouts = [
        name
        for text in audits
        for name in re.findall(
            r"(?m)^#print axioms YangMills\.RG\.([^\s]+)\s*$", text
        )
    ]
    if tuple(declarations) != EXPECTED:
        raise SystemExit(f"C6D_EQ335_DECLARATION_MISMATCH={declarations!r}")
    if tuple(readouts) != EXPECTED:
        raise SystemExit(f"C6D_EQ335_AUDIT_READOUT_MISMATCH={readouts!r}")
    joined = "\n".join(sources)
    required = (
        "∀ C : CMP99SourceRegularCube",
        "Nonempty (CMP99Eq335PhysicalCubeRegularityData C U eta alpha0)",
        "Classical.choice (R.onCube C)",
        "let W := R.toCubeWitness C alpha1 hscale",
        "CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C",
    )
    missing = [token for token in required if token not in joined]
    if missing:
        raise SystemExit(f"C6D_EQ335_REQUIRED_MECHANISM_MISSING={missing!r}")
    consumer = sources[1]
    forbidden = (
        "(W : CMP99Eq335PhysicalRegularityWitness",
        "fineSmall :",
        "value_bound :",
        "left_derivative_bound :",
        "right_adjoint_derivative_bound :",
        "laplacian_bound :",
    )
    present = [token for token in forbidden if token in consumer]
    if present:
        raise SystemExit(f"C6D_EQ335_FORBIDDEN_RENAMING_PRESENT={present!r}")


def manifest_digest(rows: list[tuple[str, bytes]]) -> str:
    payload = "".join(
        f"{sha256(data)}  {relative}\n" for relative, data in rows
    ).encode()
    return sha256(payload)


def main() -> int:
    paths = read_paths()
    rows = read_layer(paths)
    check_surface(paths)
    digest = manifest_digest(rows)
    if digest != PROMOTED_MANIFEST_SHA256:
        raise SystemExit(f"C6D_EQ335_PROMOTED_MANIFEST_MISMATCH={digest}")
    print(
        "C6D_EQ335_PROMOTION_PREVIEW_OK "
        f"files={len(rows)} declarations=5 audit_readouts=5 "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
