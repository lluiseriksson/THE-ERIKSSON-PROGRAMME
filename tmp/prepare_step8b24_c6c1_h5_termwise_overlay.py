#!/usr/bin/env python3
"""Prepare the deterministic PRE-VALIDATION H5a--H5c termwise overlay.

This is a mechanical draft-to-public-name transformation only.  It does not
compile Lean, alter tracked files, transport a tsum, prove an owner metric
dictionary, attain window 15 or discharge a terminal field.
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
OVERLAY = TMP / "step8b24-c6c1-h5-termwise-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H5-TERMWISE-OVERLAY-MANIFEST.json"

INPUTS = (
    (
        TMP / "BalabanCMP89Eq249MassUniformRealSliceRecombination.draft.lean",
        "9A38D0E4277A035C902206B984620106DBBD36881308778B528D59CB8366B5AA",
        Path("YangMills/RG/BalabanCMP89Eq249MassUniformRealSliceRecombination.lean"),
        1,
        False,
    ),
    (
        TMP / "BalabanCMP89Eq249MassUniformRealSliceRecombinationAudit.draft.lean",
        "BB12D95F380B1BE43992588F6733CE2789C2BE748FD8C412A5E33787EDDF65E8",
        Path("YangMills/RG/BalabanCMP89Eq249MassUniformRealSliceRecombinationAudit.lean"),
        1,
        True,
    ),
    (
        TMP / "BalabanCMP99SourceSeparatedPhysicalHolderTermwiseBridge.draft.lean",
        "8DE98F2CB90E096554E2372B7D2FBAFB0F22519B52297C72242F8F0306CE771E",
        Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderTermwiseBridge.lean"),
        2,
        False,
    ),
    (
        TMP / "BalabanCMP99SourceSeparatedPhysicalHolderTermwiseBridgeAudit.draft.lean",
        "22CBFB16189C01FAE1ABC02E9C1104C42F4627A4B447CC9EB2A4DC60BE26261B",
        Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderTermwiseBridgeAudit.lean"),
        2,
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


def require_independent_directions(text: str) -> None:
    code = strip_lean_comments(text)
    required = (
        "(derivMu bondNu : Fin 4)",
        "cmp89Eq248FineLatticeForwardCoordinateShift bondNu u",
        "cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)",
        "mass a derivMu u n.1",
        "mass a derivMu forwardU n.1",
    )
    for marker in required:
        if marker not in code:
            raise AssertionError(f"INDEPENDENT_DIRECTION_MARKER_MISSING={marker}")


def build_payload() -> tuple[list[tuple[Path, bytes]], dict[str, object]]:
    rows: list[tuple[Path, bytes]] = []
    input_hashes: dict[str, str] = {}
    for draft, expected, target, count, audit in INPUTS:
        content = promote(read_pinned(draft, expected), count, audit)
        rows.append((target, content))
        input_hashes[draft.name] = expected
    require_independent_directions(rows[2][1].decode("utf-8"))
    records = [
        {"path": path.as_posix(), "sha256": sha256(content), "bytes": len(content)}
        for path, content in rows
    ]
    payload: dict[str, object] = {
        "status": "PRE-VALIDATION",
        "compiler_verified": False,
        "scope": "H5a mass-uniform real slice plus H5b/H5c termwise physical-bond bridge",
        "positive_mass_premise": "ABSENT",
        "derivative_and_bond_directions": "INDEPENDENT",
        "tsum_transport": "OPEN",
        "owner_metric_dictionary": "OPEN",
        "window15": "OPEN",
        "terminal_fields": "OPEN",
        "input_sha256": input_hashes,
        "files": records,
        "declarations": 3,
        "axiom_prints": 3,
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
        "declarations": 3,
        "axiom_prints": 3,
        "manifest_sha256": sha256(manifest_bytes),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "peak_rss_bytes": peak_rss_bytes(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
