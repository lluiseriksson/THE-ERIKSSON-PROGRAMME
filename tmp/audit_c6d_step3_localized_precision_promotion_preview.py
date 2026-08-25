#!/usr/bin/env python3
"""Read-only, fail-closed preview for the six-file C6d step-3 layer."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PATH_LIST = ROOT / "tmp" / "C6D-STEP3-LOCALIZED-PRECISION-DRAFT-PATHS.txt"
PATH_LIST_SHA256 = "0BC2575014A4A6CB23B9DA6677D0FAFA44BBD0501595916A510670CD805B850C"
RAW_AGGREGATE_SHA256 = "5BBAF08BDE03699D8225581ACE32BBC1C094EC70B031A6CA51E4CF115BD10A90"
PROMOTED_MANIFEST_SHA256 = "2BECC005430EE05217A39AD08CF127DE9B3519095E26836CB4CC5D718908DFD7"

EXPECTED = (
    "norm_covariantD0CLM_extendZero_eq_of_eqOn_internalBonds",
    "norm_cmp99ActiveRegionSourceCovariantD0CLM_eq_of_eqOn_internalBonds",
    "cmp99ActiveRegionSourceCovariantLaplacian_eq_of_eqOn_internalBonds",
    "CMP99Eq335PhysicalRegularityWitness."
    "transformedBackground_eq_exponential_on_internalBonds",
    "CMP99Eq335PhysicalRegularityWitness."
    "regionalLaplacian_eq_exponential_of_sourceRegionDictionary",
    "CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision",
    "CMP99Eq335PhysicalRegularityClass.localizedRetainedPhysicalPrecision_eq",
    "CMP99Eq335PhysicalRegularityClass."
    "localizedRetainedPhysicalPrecision_eq_canonical",
    "CMP99Eq335PhysicalRegularityClass."
    "localizedRetainedPhysicalPrecision_eq_exponentialSource",
    "CMP99Eq335PhysicalRegularityClass."
    "localizedRetainedPhysicalPrecision_isSymmetric",
    "CMP99Eq335PhysicalRegularityClass.inner_localizedRetainedPhysicalPrecision",
)

PREREQUISITE_TARGETS = (
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityLaplacianLocality.lean",
    "YangMills/RG/BalabanCMP99Eq335SourceRegionDictionary.lean",
    "YangMills/RG/"
    "BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower.lean",
    "YangMills/RG/BalabanCMP99SourceRetainedPhysicalPrecision.lean",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def read_paths() -> list[str]:
    if not PATH_LIST.is_file():
        raise SystemExit("C6D_STEP3_PATH_LIST_MISSING")
    if sha256(PATH_LIST.read_bytes()) != PATH_LIST_SHA256:
        raise SystemExit("C6D_STEP3_PATH_LIST_HASH_MISMATCH")
    paths = [
        line.strip()
        for line in PATH_LIST.read_text(encoding="utf-8-sig").splitlines()
        if line.strip()
    ]
    if len(paths) != 6 or len(set(paths)) != 6:
        raise SystemExit(f"C6D_STEP3_PATH_SCOPE={len(paths)}/{len(set(paths))}")
    if any(not path.startswith("tmp/") or not path.endswith(".draft.lean") for path in paths):
        raise SystemExit("C6D_STEP3_PATH_OUTSIDE_SCRATCH")
    return paths


def promoted_target(relative: str) -> str:
    return "YangMills/RG/" + Path(relative).name.replace(".draft.lean", ".lean")


def read_layer(paths: list[str]) -> list[tuple[str, bytes]]:
    rows: list[tuple[str, bytes]] = []
    raw_lines: list[str] = []
    for relative in paths:
        path = ROOT / relative
        if not path.is_file():
            raise SystemExit(f"C6D_STEP3_RAW_MISSING={relative}")
        data = path.read_bytes()
        raw_lines.append(f"{sha256(data)}  {relative}\n")
        text = data.decode("utf-8-sig")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"C6D_STEP3_PREVALIDATION_COUNT={relative}")
        if re.search(r"(?m)^\s*(?:sorry|admit|axiom)\b", text):
            raise SystemExit(f"C6D_STEP3_FORBIDDEN_DECLARATION={relative}")
        target = promoted_target(relative)
        if (ROOT / target).exists():
            raise SystemExit(f"C6D_STEP3_TARGET_EXISTS={target}")
        rows.append((target, data.replace(b"\r\n", b"\n")))
    if sha256("".join(raw_lines).encode()) != RAW_AGGREGATE_SHA256:
        raise SystemExit("C6D_STEP3_RAW_AGGREGATE_HASH_MISMATCH")
    return rows


def check_surface(paths: list[str]) -> None:
    sources = "\n".join(
        (ROOT / path).read_text(encoding="utf-8-sig")
        for path in paths
        if not path.endswith("Audit.draft.lean")
    )
    audits = "\n".join(
        (ROOT / path).read_text(encoding="utf-8-sig")
        for path in paths
        if path.endswith("Audit.draft.lean")
    )
    missing_sources = [name for name in EXPECTED if sources.count(name) < 1]
    if missing_sources:
        raise SystemExit(f"C6D_STEP3_DECLARATION_MISSING={missing_sources!r}")
    readouts = re.findall(r"(?m)^#print axioms (?:YangMills\.RG\.)?([^\s]+)\s*$", audits)
    if len(readouts) != len(EXPECTED) or set(readouts) != set(EXPECTED):
        raise SystemExit(f"C6D_STEP3_AUDIT_READOUT_MISMATCH={readouts!r}")
    required = (
        "rho.norm_ad",
        "inner_map_self_eq_zero",
        "Omega.bonds",
        "printed_omegaPrime0_subset_regularCube",
        "cmp99SourceGaugePrecision",
        "W.transformedBackground eta",
        "(matrixSUNAdjointModel Nc)",
        "localizedTowerAt (Fin.last depth)",
        "canonicalTowerAt (Fin.last depth)",
        "inner_cmp99SourceGaugePrecision",
    )
    missing = [token for token in required if token not in sources]
    if missing:
        raise SystemExit(f"C6D_STEP3_REQUIRED_MECHANISM_MISSING={missing!r}")
    consumer = (ROOT / paths[4]).read_text(encoding="utf-8-sig")
    forbidden = (
        "(precision :",
        "(Qprime :",
        "(Green :",
        "(coercivity :",
        "(W : CMP99Eq335PhysicalRegularityWitness",
        "{eta alpha0 alpha1 spacing : ℝ}",
    )
    present = [token for token in forbidden if token in consumer]
    if present:
        raise SystemExit(f"C6D_STEP3_FORBIDDEN_CALLER_INPUT={present!r}")


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
        raise SystemExit(f"C6D_STEP3_PROMOTED_MANIFEST_MISMATCH={digest}")
    print(
        "C6D_STEP3_PROMOTION_PREVIEW_OK "
        f"files={len(rows)} declarations={len(EXPECTED)} "
        f"audit_readouts={len(EXPECTED)} manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
