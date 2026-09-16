#!/usr/bin/env python3
"""Prepare the deterministic PRE-VALIDATION overlay for H4a/H4b endpoint swap.

The script performs only a mechanical draft-to-public-name transformation.  It
does not compile Lean, alter tracked files, or claim source/owner metric
identification.
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
OVERLAY = TMP / "step8b24-c6c1-h4-swap-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H4-SWAP-OVERLAY-MANIFEST.json"

SOURCE_DRAFT = TMP / "BalabanCMP89Eq249CompleteHolderEndpointSwap.draft.lean"
AUDIT_DRAFT = TMP / "BalabanCMP89Eq249CompleteHolderEndpointSwapAudit.draft.lean"

SOURCE_INPUT_SHA256 = (
    "3E62B6F441962753D37F8F58F8AF595D05F8BC1305D93631954E0C42660DECF1"
)
AUDIT_INPUT_SHA256 = (
    "6B804B0DC794B6DA9F4EC90C1AF16B44F561A2788FB38AE5E5E9BA051FF1B145"
)

SOURCE_TARGET = Path("YangMills/RG/BalabanCMP89Eq249CompleteHolderEndpointSwap.lean")
AUDIT_TARGET = Path(
    "YangMills/RG/BalabanCMP89Eq249CompleteHolderEndpointSwapAudit.lean"
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


def read_pinned(path: Path, expected: str) -> str:
    raw = path.read_bytes()
    actual = sha256(raw)
    if actual != expected:
        raise AssertionError(f"INPUT_SHA256_MISMATCH={path.name}/{actual}")
    return raw.decode("utf-8")


def promote_source(text: str) -> bytes:
    promoted = text.replace("_draft", "")
    promoted = promoted.replace(
        "This source is present only as a static draft.  Its `.olean` has not been\n"
        "materialized and none of the declarations below has been compiler-verified.",
        "This source is present at PRE-VALIDATION.  Its `.olean` has not been\n"
        "materialized and none of the declarations below has been compiler-verified.",
    )
    if "_draft" in promoted:
        raise AssertionError("SOURCE_DRAFT_SUFFIX_SURVIVED")
    if promoted.count("PRE-VALIDATION:") != 1:
        raise AssertionError("SOURCE_PRE_MARKER_COUNT")
    declarations = re.findall(
        r"(?m)^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|structure)\s+([A-Za-z0-9_']+)",
        promoted,
    )
    if len(declarations) != 12 or len(declarations) != len(set(declarations)):
        raise AssertionError(f"SOURCE_DECLARATION_COUNT={len(declarations)}")
    for forbidden in ("sorry", "admit", "axiom "):
        if forbidden in promoted:
            raise AssertionError(f"SOURCE_FORBIDDEN={forbidden.strip()}")
    required = (
        "cmp89Eq251ComplexStabilizedIntegrand_physicalFine_eq_orientation_mul_nearest",
        "cmp89Eq249PhysicalFineLatticeDisplacement xi holder",
        "cmp89Eq249PhysicalFineLatticeDisplacement xi transport",
        "cmp89Eq251LatticeL1Length_nearestEndpointTransport_eq_min",
    )
    for marker in required:
        if marker not in promoted:
            raise AssertionError(f"SOURCE_PHYSICAL_MARKER_MISSING={marker}")
    return promoted.replace("\r\n", "\n").encode("utf-8")


def promote_audit(text: str) -> bytes:
    promoted = text.replace(
        "# PRE-VALIDATION audit: complete CMP89 Holder endpoint swap",
        "# PRE-VALIDATION: audit complete CMP89 Holder endpoint swap",
    ).replace(
        "The target source is still a scratch draft.  Its `.olean` has not been\n"
        "materialized and these readouts have not been executed by Lean.",
        "The target source remains PRE-VALIDATION.  Its `.olean` has not been\n"
        "materialized and these readouts have not been executed by Lean.",
    )
    if "_draft" in promoted:
        raise AssertionError("AUDIT_DRAFT_SUFFIX_SURVIVED")
    if promoted.count("PRE-VALIDATION:") != 1:
        raise AssertionError("AUDIT_PRE_MARKER_COUNT")
    targets = re.findall(r"(?m)^#print axioms ([^\s]+)$", promoted)
    if len(targets) != 7 or len(targets) != len(set(targets)):
        raise AssertionError(f"AUDIT_AXIOM_COUNT={len(targets)}")
    expected_import = "import YangMills.RG.BalabanCMP89Eq249CompleteHolderEndpointSwap"
    if promoted.count(expected_import) != 1:
        raise AssertionError("AUDIT_IMPORT_COUNT")
    return promoted.replace("\r\n", "\n").encode("utf-8")


def build_payload() -> tuple[list[tuple[Path, bytes]], dict[str, object]]:
    source = promote_source(read_pinned(SOURCE_DRAFT, SOURCE_INPUT_SHA256))
    audit = promote_audit(read_pinned(AUDIT_DRAFT, AUDIT_INPUT_SHA256))
    rows = [(SOURCE_TARGET, source), (AUDIT_TARGET, audit)]
    records = [
        {"path": path.as_posix(), "sha256": sha256(content), "bytes": len(content)}
        for path, content in rows
    ]
    payload: dict[str, object] = {
        "status": "PRE-VALIDATION",
        "compiler_verified": False,
        "scope": "H4a/H4b exact endpoint selection and antisymmetry only",
        "physical_fine_displacements": "BOTH_LITERAL",
        "source_metric_dictionary": "OPEN",
        "complete_holder_bound": "OPEN",
        "input_sha256": {
            SOURCE_DRAFT.name: SOURCE_INPUT_SHA256,
            AUDIT_DRAFT.name: AUDIT_INPUT_SHA256,
        },
        "files": records,
        "declarations": 12,
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
    manifest_bytes = (
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    MANIFEST.write_bytes(manifest_bytes)
    result = {
        "status": "PASS",
        "compiler_verified": False,
        "files": len(rows),
        "declarations": 12,
        "axiom_prints": 7,
        "manifest_sha256": sha256(manifest_bytes),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "peak_rss_bytes": peak_rss_bytes(),
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
