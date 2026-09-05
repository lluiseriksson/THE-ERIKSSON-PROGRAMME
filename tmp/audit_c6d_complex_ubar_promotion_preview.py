#!/usr/bin/env python3
"""Read-only, fail-closed preview for the six-file complex Ubar layer."""

from __future__ import annotations

import hashlib
import importlib.util
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PATH_LIST = ROOT / "tmp" / "C6D-COMPLEX-UBAR-DRAFT-PATHS.txt"
PATH_LIST_SHA256 = "3F97087928E61572A8552A6F6A3D737EEA50BC86BD4D1C4A8863E13B33B6F3EF"
RAW_AGGREGATE_SHA256 = "78A68FAE7A74EBFF6F056756191C19197CA5744670B5A519E795E06D59CCFFCE"
PROMOTED_MANIFEST_SHA256 = "EAF815BF6D97C069A1887F755A4DF606B2B890BE910E2533AB716049097CF603"

EXPECTED = (
    "instMatrixRealizationSpecialLinear",
    "matrixTraceQuantized_nearLog_sub_one_of_det_eq_one",
    "trace_nearLog_sub_one_eq_zero_of_det_eq_one_of_noWinding",
    "cmp99UbarSpecialLinearExponent",
    "trace_cmp99UbarSpecialLinearExponent_eq_zero",
    "cmp99UbarSpecialLinearFactorOfNearIdentity",
    "cmp99UbarSpecialLinearFactorOfNearIdentity_coe",
    "cmp99UbarSpecialLinearBlockOfNearIdentity",
    "cmp99UbarSpecialLinearBlockOfNearIdentity_coe",
    "cmp99UbarSpecialLinearFactorOfDeviationBudget",
    "cmp99UbarSpecialLinearFactorOfDeviationBudget_coe",
    "cmp99UbarSpecialLinearBlockOfDeviationBudget",
    "cmp99UbarSpecialLinearBlockOfDeviationBudget_coe",
    "cmp99SUNLieComplexCoordMatrixCLM",
    "cmp99SUNLieComplexCoordMatrixNormBudget",
    "norm_cmp99SUNLieComplexCoordMatrixLM_le",
    "cmp99UbarSpecialLinearExponentSl",
    "cmp99UbarSpecialLinearExponentSl_val",
    "cmp99UbarSpecialLinearExponentCoord",
    "cmp99SUNLieComplexCoordMatrixLM_exponentCoord",
    "cmp99UbarSpecialLinearFactorOfNearIdentity_coe_eq_exp_coord",
    "cmp99SourceComplexLocalizedUbarDeviation",
    "cmp99SourceComplexLocalizedUbarBlock",
    "cmp99SourceComplexLocalizedNextBackground",
    "cmp99SourceComplexLocalizedNextBackground_apply_pos",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def load_coverage_guard():
    path = ROOT / "scripts" / "check_lean_axiom_readout_coverage.py"
    spec = importlib.util.spec_from_file_location("c6d_complex_ubar_coverage", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_COMPLEX_UBAR_COVERAGE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def read_paths() -> list[str]:
    if not PATH_LIST.is_file():
        raise RuntimeError("C6D_COMPLEX_UBAR_PATH_LIST_MISSING")
    if sha256(PATH_LIST.read_bytes()) != PATH_LIST_SHA256:
        raise RuntimeError("C6D_COMPLEX_UBAR_PATH_LIST_HASH_MISMATCH")
    paths = [
        line.strip()
        for line in PATH_LIST.read_text(encoding="utf-8-sig").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if len(paths) != 6 or len(set(paths)) != 6:
        raise RuntimeError(f"C6D_COMPLEX_UBAR_PATH_SCOPE={len(paths)}/{len(set(paths))}")
    if any(not path.startswith("tmp/") or not path.endswith(".draft.lean") for path in paths):
        raise RuntimeError("C6D_COMPLEX_UBAR_PATH_OUTSIDE_SCRATCH")
    return paths


def promoted_target(relative: str) -> str:
    return "YangMills/RG/" + Path(relative).name.replace(".draft.lean", ".lean")


def read_layer(paths: list[str]) -> list[tuple[str, bytes]]:
    rows: list[tuple[str, bytes]] = []
    raw_lines: list[str] = []
    for relative in paths:
        path = ROOT / relative
        if not path.is_file():
            raise RuntimeError(f"C6D_COMPLEX_UBAR_RAW_MISSING={relative}")
        data = path.read_bytes()
        raw_lines.append(f"{sha256(data)}  {relative}\n")
        text = data.decode("utf-8-sig")
        if text.count("PRE-VALIDATION:") != 1:
            raise RuntimeError(f"C6D_COMPLEX_UBAR_PREVALIDATION_COUNT={relative}")
        if re.search(r"(?m)^\s*(?:sorry|admit|axiom)\b", text):
            raise RuntimeError(f"C6D_COMPLEX_UBAR_FORBIDDEN_DECLARATION={relative}")
        target = promoted_target(relative)
        if (ROOT / target).exists():
            raise RuntimeError(f"C6D_COMPLEX_UBAR_TARGET_EXISTS={target}")
        rows.append((target, data.replace(b"\r\n", b"\n")))
    if sha256("".join(raw_lines).encode()) != RAW_AGGREGATE_SHA256:
        raise RuntimeError("C6D_COMPLEX_UBAR_RAW_AGGREGATE_HASH_MISMATCH")
    return rows


def check_surface(paths: list[str]) -> None:
    guard = load_coverage_guard()
    resolved = [ROOT / path for path in paths]
    failures = guard.coverage_failures(resolved)
    if failures:
        raise RuntimeError("C6D_COMPLEX_UBAR_COVERAGE=" + repr(failures))
    sources = [path for path in resolved if not guard.is_audit(path)]
    declarations = guard.declaration_names(sources)
    if tuple(declarations) != EXPECTED:
        raise RuntimeError("C6D_COMPLEX_UBAR_DECLARATIONS=" + repr(declarations))
    text = "\n".join(path.read_text(encoding="utf-8-sig") for path in sources)
    required = (
        "Complex.exp_eq_one_iff",
        "trace_eq_zero_of_quantized_of_norm_lt_two_pi",
        "det_matrix_exp_eq_exp_trace",
        "(cmp99SUNLieComplexCoordSlEquiv Nc).symm",
        "cmp99SUNLieComplexCoordMatrixLM Nc",
        "cmp99SUNLieComplexCoordMatrixCLM Nc",
        "cmp99SUNLieComplexCoordMatrixNormBudget Nc",
        "MatrixNearLogNoWindingBudget Nc",
        "(M ^ d : ℝ)⁻¹",
        "gaugeConfigOfPositiveBonds",
    )
    missing = [token for token in required if token not in text]
    if missing:
        raise RuntimeError("C6D_COMPLEX_UBAR_MECHANISM_MISSING=" + repr(missing))
    forbidden = (
        "(exponentCoord : SUNLieComplexCoord",
        "(nextBackground : GaugeConfig",
        "(UbarBlock :",
        "(traceZero :",
    )
    present = [token for token in forbidden if token in text]
    if present:
        raise RuntimeError("C6D_COMPLEX_UBAR_FREE_OUTPUT=" + repr(present))


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
        raise RuntimeError(f"C6D_COMPLEX_UBAR_PROMOTED_MANIFEST_MISMATCH={digest}")
    print(
        "C6D_COMPLEX_UBAR_PROMOTION_PREVIEW_OK "
        f"files={len(rows)} declarations={len(EXPECTED)} "
        f"audit_readouts={len(EXPECTED)} manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
