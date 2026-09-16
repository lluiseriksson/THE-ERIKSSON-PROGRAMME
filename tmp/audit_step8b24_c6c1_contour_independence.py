#!/usr/bin/env python3
"""Static fail-closed audit for the CMP89 H3/H4 contour prefix.

This is deliberately not a Lean verifier.  It establishes the narrower design
fact needed while CMP95 printed page 35 is unavailable: the reviewed contour
prefix does not consume a local Holder seminorm, a ready-made Holder bound,
regional B0, a terminal field, or a TermSource.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
import time
import ctypes
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

FILES = {
    "BalabanCMP89Eq248GreenOneCoordinateContourShift.draft.lean": {
        "sha256": "561FA0637AC7A7B1B536201695995A323EFB4197CF466EA49B108C62BD15F3E0",
        "imports": {
            "YangMills.RG.HolomorphicVerticalShiftBoundary",
            "YangMills.RG.BalabanCMP89Eq251OneCoordinateContourShift",
            "YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy",
        },
        "declarations": {
            "intervalIntegral_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_coordinateShift_draft",
        },
        "required": {
            "CMP89Eq249UniformNoncentralComplexRadiusCondition",
            "CMP89Eq249CentralStabilizedComplexWindow",
            "CMP89Eq251UniformMassWindow",
            "cmp89Eq248ComplexStabilizedGreenEndpointIntegrand",
        },
    },
    "BalabanCMP89Eq248GreenProductContourTelescope.draft.lean": {
        "sha256": "91DC9453B4B1F1B722E9CB7763B90F582DC4EBE68210846186778B954E97AD57",
        "imports": {
            "YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductIntegrability",
            "YangMills.RG.BalabanCMP89Eq248GreenOneCoordinateContourShift",
        },
        "declarations": {
            "cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft",
            "integrable_cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft",
            "integral_cmp89Eq248FineLatticeGreenPartialProductIntegrand_stage_succ_draft",
            "integral_cmp89Eq248FineLatticeGreenPartialProductIntegrand_zero_eq_four_draft",
            "integral_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_eq_signed_massUniform_draft",
        },
        "required": {
            "CMP89Eq249UniformNoncentralComplexRadiusCondition",
            "CMP89Eq249CentralStabilizedComplexWindow",
            "CMP89Eq251UniformMassWindow",
            "intervalIntegral_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_coordinateShift_draft",
        },
    },
    "BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift.draft.lean": {
        "sha256": "49B197322233828D2C3D874DD4678A0758773FFF221B9EDBACE0EB7CFAAA2502",
        "imports": {
            "YangMills.RG.HolomorphicVerticalShiftBoundary",
            "YangMills.RG.BalabanCMP89Eq251OneCoordinateContourShift",
            "YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformHolomorphy",
        },
        "declarations": {
            "intervalIntegral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_coordinateShift_massUniform_draft",
        },
        "required": {
            "CMP89Eq249UniformNoncentralComplexRadiusCondition",
            "CMP89Eq249CentralStabilizedComplexWindow",
            "CMP89Eq251UniformMassWindow",
            "cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand",
        },
    },
    "BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope.draft.lean": {
        "sha256": "8EA1CAD775A5FAFFC1BDDC63A7D130ED917AEA93B3C4F5D69ED167A19031E5B0",
        "imports": {
            "YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductIntegrability",
            "YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift",
        },
        "declarations": {
            "cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft",
            "integrable_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft",
            "integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_stage_succ_draft",
            "integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_zero_eq_four_draft",
            "integral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_eq_signed_massUniform_draft",
        },
        "required": {
            "CMP89Eq249UniformNoncentralComplexRadiusCondition",
            "CMP89Eq249CentralStabilizedComplexWindow",
            "CMP89Eq251UniformMassWindow",
            "intervalIntegral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_coordinateShift_massUniform_draft",
        },
    },
    "BalabanCMP89Eq249CompleteHolderEndpointSwap.draft.lean": {
        "sha256": "3E62B6F441962753D37F8F58F8AF595D05F8BC1305D93631954E0C42660DECF1",
        "imports": {
            "YangMills.RG.BalabanCMP89Eq251ComplexContourPhase",
            "YangMills.RG.BalabanCMP89Eq251StabilizedEndpointRecombination",
        },
        "declarations": {
            "cmp89Eq251EuclideanNorm_neg_draft",
            "cmp89Eq251ComplexBareAliasNumerator_swap_draft",
            "cmp89Eq251ComplexStabilizedNumerator_swap_draft",
            "cmp89Eq251ComplexStabilizedIntegrand_swap_draft",
            "cmp89Eq249HolderFirstEndpointDisplacement_draft",
            "cmp89Eq249NearestEndpointUsesTransport_draft",
            "cmp89Eq249NearestEndpointHolder_draft",
            "cmp89Eq249NearestEndpointTransport_draft",
            "cmp89Eq249NearestEndpointOrientation_draft",
            "cmp89Eq251LatticeL1Length_nearestEndpointTransport_eq_min_draft",
            "cmp89Eq249NearestEndpointHolder_unit_draft",
            "cmp89Eq251ComplexStabilizedIntegrand_physicalFine_eq_orientation_mul_nearest_draft",
        },
        "required": {
            "cmp89Eq251LatticeL1Length",
            "min",
            "cmp89Eq251ComplexStabilizedIntegrand_swap_draft",
        },
    },
}

AUDITS = {
    "BalabanCMP89Eq248GreenOneCoordinateContourShiftAudit.draft.lean": {
        "sha256": "07E296425C789CE2622E7AAB917205F83CFD592E41E90936955EE57719AA3E33",
        "imports": set(),
        "axioms": {
            "YangMills.RG.intervalIntegral_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_coordinateShift_draft",
        },
    },
    "BalabanCMP89Eq248GreenProductContourTelescopeAudit.draft.lean": {
        "sha256": "54047957543C636781F2E359C96635FB858C80BC5FA3DCB72A92520F860DF424",
        "imports": set(),
        "axioms": {
            "YangMills.RG.cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft",
            "YangMills.RG.integrable_cmp89Eq248FineLatticeGreenPartialProductIntegrand_draft",
            "YangMills.RG.integral_cmp89Eq248FineLatticeGreenPartialProductIntegrand_stage_succ_draft",
            "YangMills.RG.integral_cmp89Eq248FineLatticeGreenPartialProductIntegrand_zero_eq_four_draft",
            "YangMills.RG.integral_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_eq_signed_massUniform_draft",
        },
    },
    "BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShiftAudit.draft.lean": {
        "sha256": "CB0D905B4D82AFE63AFE7DCDB80E61D76D9AA34FAE51901CB685AD815344527A",
        "imports": {
            "YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift",
        },
        "axioms": {
            "YangMills.RG.intervalIntegral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_coordinateShift_massUniform_draft",
        },
    },
    "BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescopeAudit.draft.lean": {
        "sha256": "8EB3F893ECF643D2137B38920CBA7C5F847FB0538760A33F7FCEE56400BBA444",
        "imports": {
            "YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope",
        },
        "axioms": {
            "YangMills.RG.cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft",
            "YangMills.RG.integrable_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft",
            "YangMills.RG.integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_stage_succ_draft",
            "YangMills.RG.integral_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_zero_eq_four_draft",
            "YangMills.RG.integral_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_eq_signed_massUniform_draft",
        },
    },
    "BalabanCMP89Eq249CompleteHolderEndpointSwapAudit.draft.lean": {
        "sha256": "6B804B0DC794B6DA9F4EC90C1AF16B44F561A2788FB38AE5E5E9BA051FF1B145",
        "imports": {
            "YangMills.RG.BalabanCMP89Eq249CompleteHolderEndpointSwap",
        },
        "axioms": {
            "YangMills.RG.cmp89Eq251EuclideanNorm_neg",
            "YangMills.RG.cmp89Eq251ComplexBareAliasNumerator_swap",
            "YangMills.RG.cmp89Eq251ComplexStabilizedNumerator_swap",
            "YangMills.RG.cmp89Eq251ComplexStabilizedIntegrand_swap",
            "YangMills.RG.cmp89Eq251LatticeL1Length_nearestEndpointTransport_eq_min",
            "YangMills.RG.cmp89Eq249NearestEndpointHolder_unit",
            "YangMills.RG.cmp89Eq251ComplexStabilizedIntegrand_physicalFine_eq_orientation_mul_nearest",
        },
    },
}

FORBIDDEN_CODE = {
    "sorry",
    "admit",
    "axiom",
    "holderSeminorm",
    "HolderSeminorm",
    "holderBound",
    "HolderBound",
    "CMP95",
    "CMP96",
    "TermSource",
    "regionalB0",
    "sourceBound",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def peak_rss_bytes() -> int:
    """Return this process's measured peak resident/working-set size."""
    if os.name == "nt":
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
        handle = get_current_process()
        get_process_memory_info = ctypes.windll.psapi.GetProcessMemoryInfo
        get_process_memory_info.argtypes = [
            ctypes.c_void_p,
            ctypes.POINTER(ProcessMemoryCounters),
            ctypes.c_ulong,
        ]
        get_process_memory_info.restype = ctypes.c_int
        ok = get_process_memory_info(
            handle, ctypes.byref(counters), counters.cb
        )
        if not ok:
            raise OSError("GetProcessMemoryInfo failed")
        return int(counters.PeakWorkingSetSize)
    import resource

    value = int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    return value if sys.platform == "darwin" else value * 1024


def strip_comments_and_strings(text: str) -> str:
    """Remove Lean comments and string contents, retaining code shape."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or in_string:
        raise AssertionError("unterminated comment or string")
    return "".join(out)


def declaration_names(code: str) -> set[str]:
    pattern = re.compile(
        r"(?m)^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|structure)\s+([A-Za-z0-9_']+)"
    )
    return set(pattern.findall(code))


def audit(root: Path = ROOT) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    audit_rows: list[dict[str, object]] = []
    total_declarations = 0
    for name, spec in FILES.items():
        path = root / "tmp" / name
        raw = path.read_bytes()
        actual_hash = sha256(raw)
        assert actual_hash == spec["sha256"], (
            f"{name}: SHA256 mismatch {actual_hash} != {spec['sha256']}"
        )
        text = raw.decode("utf-8")
        code = strip_comments_and_strings(text)

        imports = set(re.findall(r"(?m)^\s*import\s+([^\s]+)\s*$", code))
        assert imports == spec["imports"], (
            f"{name}: imports {sorted(imports)} != {sorted(spec['imports'])}"
        )

        declarations = declaration_names(code)
        assert declarations == spec["declarations"], (
            f"{name}: declarations {sorted(declarations)} != "
            f"{sorted(spec['declarations'])}"
        )

        for token in FORBIDDEN_CODE:
            assert not re.search(rf"\b{re.escape(token)}\b", code), (
                f"{name}: forbidden code token {token}"
            )
        for token in spec["required"]:
            assert token in code, f"{name}: missing required token {token}"

        total_declarations += len(declarations)
        rows.append(
            {
                "path": f"tmp/{name}",
                "sha256": actual_hash,
                "imports": sorted(imports),
                "declarations": sorted(declarations),
            }
        )

    axiom_blocks = 0
    for name, spec in AUDITS.items():
        path = root / "tmp" / name
        raw = path.read_bytes()
        actual_hash = sha256(raw)
        assert actual_hash == spec["sha256"], (
            f"{name}: SHA256 mismatch {actual_hash} != {spec['sha256']}"
        )
        code = strip_comments_and_strings(raw.decode("utf-8"))
        imports = set(re.findall(r"(?m)^\s*import\s+([^\s]+)\s*$", code))
        assert imports == spec["imports"], (
            f"{name}: imports {sorted(imports)} != {sorted(spec['imports'])}"
        )
        targets = set(re.findall(r"(?m)^\s*#print\s+axioms\s+([^\s]+)\s*$", code))
        assert targets == spec["axioms"], (
            f"{name}: axiom targets {sorted(targets)} != {sorted(spec['axioms'])}"
        )
        axiom_blocks += len(targets)
        audit_rows.append(
            {
                "path": f"tmp/{name}",
                "sha256": actual_hash,
                "imports": sorted(imports),
                "axiom_targets": sorted(targets),
            }
        )

    return {
        "status": "PASS",
        "scope": "static-design-only",
        "compiler_verified": False,
        "source_files": len(rows),
        "audit_files": len(audit_rows),
        "declarations": total_declarations,
        "axiom_blocks": axiom_blocks,
        "cmp95_page_35_required_for_complete_holder": True,
        "contour_prefix_independent_of_cmp95_seminorm": True,
        "files": rows,
        "audits": audit_rows,
    }


def main() -> int:
    started = time.perf_counter()
    try:
        result = audit()
    except (AssertionError, OSError, UnicodeError) as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}, sort_keys=True))
        return 1
    result["elapsed_seconds"] = round(time.perf_counter() - started, 6)
    result["peak_rss_bytes"] = peak_rss_bytes()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
