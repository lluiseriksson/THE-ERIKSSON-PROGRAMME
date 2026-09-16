#!/usr/bin/env python3
"""Prepare the deterministic PRE-VALIDATION H5d0a--H5d0b overlay.

This is a mechanical draft-to-public-name transformation only. It does not
compile Lean, construct the generated operator, transport a tsum or owner
metric, attain window 15, or discharge a terminal field.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h5-holder-factor-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H5-HOLDER-FACTOR-OVERLAY-MANIFEST.json"

INPUTS = (
    (
        TMP / "BalabanCMP89Eq249PhysicalHolderAlphaFactorization.draft.lean",
        "A510FC96E3C55A473CD8E3F71BE79C8FB00327D0BAD88E44B239415098AE54F2",
        Path("YangMills/RG/BalabanCMP89Eq249PhysicalHolderAlphaFactorization.lean"),
        4,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq249PhysicalHolderAlphaFactorizationAudit.draft.lean",
        "012C09CA5527B11594C434BC42207B8454176EFB4D661773B05F9DB961C1CF22",
        Path("YangMills/RG/BalabanCMP89Eq249PhysicalHolderAlphaFactorizationAudit.lean"),
        4,
        True,
    ),
    (
        TMP / "BalabanCMP89Eq249PhysicalHolderNormalizedIntegral.draft.lean",
        "714FCB23825810AC0748DA8C3CA22B05314E6A1D5E83725DDCA4C89D3462C3BE",
        Path("YangMills/RG/BalabanCMP89Eq249PhysicalHolderNormalizedIntegral.lean"),
        3,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq249PhysicalHolderNormalizedIntegralAudit.draft.lean",
        "BAE0B16BA2ADCAE3A3577D1E1CCFA3E59D2C8BA4CB57387F4710881CE108FBF1",
        Path("YangMills/RG/BalabanCMP89Eq249PhysicalHolderNormalizedIntegralAudit.lean"),
        3,
        True,
    ),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def peak_rss_bytes() -> int:
    if os.name == "nt":
        import ctypes

        class ProcessMemoryCounters(ctypes.Structure):
            _fields_ = [
                ("cb", ctypes.c_ulong),
                ("PageFaultCount", ctypes.c_ulong),
                ("PeakWorkingSetSize", ctypes.c_size_t),
                ("WorkingSetSize", ctypes.c_size_t),
                ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                ("PagefileUsage", ctypes.c_size_t),
                ("PeakPagefileUsage", ctypes.c_size_t),
            ]
        counters = ProcessMemoryCounters()
        counters.cb = ctypes.sizeof(counters)
        get_current_process = ctypes.windll.kernel32.GetCurrentProcess
        get_current_process.restype = ctypes.c_void_p
        get_process_memory_info = ctypes.windll.psapi.GetProcessMemoryInfo
        get_process_memory_info.argtypes = [
            ctypes.c_void_p,
            ctypes.POINTER(ProcessMemoryCounters),
            ctypes.c_ulong,
        ]
        get_process_memory_info.restype = ctypes.c_int
        if not get_process_memory_info(
            get_current_process(), ctypes.byref(counters), counters.cb
        ):
            raise OSError("GetProcessMemoryInfo failed")
        return int(counters.PeakWorkingSetSize)
    import resource

    value = int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    return value if sys.platform == "darwin" else value * 1024


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise AssertionError("UNTERMINATED_BLOCK_COMMENT")
    return "".join(out)


def read_pinned(path: Path, expected: str) -> str:
    raw = path.read_bytes()
    actual = sha256(raw)
    if actual != expected:
        raise AssertionError(f"INPUT_SHA256_MISMATCH={path.name}/{actual}")
    return raw.decode("utf-8")


def promote(text: str, expected_count: int, audit: bool) -> bytes:
    promoted = text.replace("_draft", "")
    if audit:
        first_newline = promoted.find("\n")
        if first_newline < 0 or not promoted.startswith("import "):
            raise AssertionError("AUDIT_IMPORT_NOT_FIRST")
        promoted = (
            promoted[: first_newline + 1]
            + "\n/- PRE-VALIDATION: source present; `.olean` not materialized; "
              "readouts not compiler-verified. -/\n"
            + promoted[first_newline + 1 :]
        )
        readouts = re.findall(r"(?m)^#print axioms ([^\s]+)$", promoted)
        if len(readouts) != expected_count or len(readouts) != len(set(readouts)):
            raise AssertionError(f"AUDIT_AXIOM_COUNT={len(readouts)}")
    else:
        promoted = promoted.replace(
            "STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.",
            "PRE-VALIDATION: source present; `.olean` not materialized; "
            "not compiler-verified.",
            1,
        )
        declarations = re.findall(
            r"(?m)^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|structure)\s+([A-Za-z0-9_']+)",
            promoted,
        )
        if len(declarations) != expected_count or len(declarations) != len(set(declarations)):
            raise AssertionError(f"SOURCE_DECLARATION_COUNT={len(declarations)}")
    if "_draft" in promoted:
        raise AssertionError("DRAFT_SUFFIX_SURVIVED")
    if promoted.count("PRE-VALIDATION:") != 1:
        raise AssertionError("PRE_MARKER_COUNT")
    code = strip_lean_comments(promoted)
    for forbidden in ("sorry", "admit", "axiom ", "by?", "exact?", "hmassPos"):
        if forbidden in code:
            raise AssertionError(f"FORBIDDEN_CODE_TOKEN={forbidden.strip()}")
    return promoted.replace("\r\n", "\n").encode("utf-8")


def require_holder_semantics(factor: str, integral: str) -> None:
    factor_code = strip_lean_comments(factor)
    integral_code = strip_lean_comments(integral)
    required_factor = (
        "cmp89Eq251ComplexBareAliasNumerator_eq_holderRpowInv_mul_zero",
        "cmp89Eq251ComplexStabilizedNumerator_eq_holderRpowInv_mul_zero",
        "cmp89Eq251ComplexStabilizedIntegrand_eq_holderRpowInv_mul_zero",
        "cmp89Eq251ComplexStabilizedIntegrand_physicalUnit_eq_xiRpowInv_mul_zero",
        "(((xi ^ alpha : ℝ) : ℂ)⁻¹)",
    )
    required_integral = (
        "def cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral",
        "cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_zero",
        "cmp89Eq249NormalizedFineLatticeStabilizedHolderIntegral_eq_xiRpowInv_mul_raw",
        "cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha",
        "integral_const_mul c _",
        "(((xi ^ alpha : ℝ) : ℂ)⁻¹)",
    )
    for marker in required_factor:
        if marker not in factor_code:
            raise AssertionError(f"HOLDER_FACTOR_MARKER_MISSING={marker}")
    for marker in required_integral:
        if marker not in integral_code:
            raise AssertionError(f"HOLDER_INTEGRAL_MARKER_MISSING={marker}")
    for forbidden in ("norm ", "‖", "window15", "TermSource"):
        if forbidden in factor_code or forbidden in integral_code:
            raise AssertionError(f"PRE_NORM_OR_TERMINAL_TOKEN={forbidden}")


def build_payload() -> tuple[list[tuple[Path, bytes]], dict[str, object]]:
    rows: list[tuple[Path, bytes]] = []
    input_hashes: dict[str, str] = {}
    for draft, expected, target, count, audit in INPUTS:
        content = promote(read_pinned(draft, expected), count, audit)
        rows.append((target, content))
        input_hashes[draft.name] = expected
    require_holder_semantics(
        rows[0][1].decode("utf-8"), rows[2][1].decode("utf-8")
    )
    records = [
        {"path": path.as_posix(), "sha256": sha256(content), "bytes": len(content)}
        for path, content in rows
    ]
    payload: dict[str, object] = {
        "status": "PRE-VALIDATION",
        "compiler_verified": False,
        "scope": "H5d0a pointwise Holder factor plus H5d0b literal general-alpha integral",
        "general_alpha_literal": True,
        "alpha_zero_identity": True,
        "xi_rpow_inverse_extracted_before_norm": True,
        "positive_mass_premise": "ABSENT",
        "generated_operator": "OPEN",
        "tsum_transport": "OPEN",
        "owner_metric_dictionary": "OPEN",
        "window15": "OPEN",
        "terminal_fields": "OPEN",
        "input_sha256": input_hashes,
        "files": records,
        "declarations": 7,
        "axiom_prints": 7,
    }
    return rows, payload


def main() -> int:
    started = time.perf_counter()
    rows, payload = build_payload()
    for relative, content in rows:
        target = OVERLAY / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
        if target.read_bytes() != content:
            raise AssertionError(f"POST_WRITE_MISMATCH={relative.as_posix()}")
    manifest_bytes = (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode()
    MANIFEST.write_bytes(manifest_bytes)
    print(json.dumps({
        "status": "PASS",
        "compiler_verified": False,
        "files": len(rows),
        "declarations": 7,
        "axiom_prints": 7,
        "manifest_sha256": sha256(manifest_bytes),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "peak_rss_bytes": peak_rss_bytes(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
