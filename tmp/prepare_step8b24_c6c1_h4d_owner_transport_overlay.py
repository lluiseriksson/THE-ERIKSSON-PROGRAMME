#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H4d two-point owner overlay."""
from __future__ import annotations
import json, time
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared

ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h4d-owner-transport-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H4D-OWNER-TRANSPORT-OVERLAY-MANIFEST.json"
SHARED_SHA256 = "D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"
INPUTS = (
    (TMP / "BalabanCMP116CMP89PhysicalNearestEndpointOwnerTransport.draft.lean",
     "BC0D5ABF811615DE9A042EAF2B0B2891B6A0E1F30E9FB53689C5B1FBEF3D97B9",
     Path("YangMills/RG/BalabanCMP116CMP89PhysicalNearestEndpointOwnerTransport.lean"), 9, False),
    (TMP / "BalabanCMP116CMP89PhysicalNearestEndpointOwnerTransportAudit.draft.lean",
     "74C4FC974432C4B0E4A084368F66B2F7CA0A918D1C3E270E4B95229F6AA49667",
     Path("YangMills/RG/BalabanCMP116CMP89PhysicalNearestEndpointOwnerTransportAudit.lean"), 9, True),
)

def require_semantics(source: str) -> None:
    code = shared.strip_lean_comments(source)
    for forbidden in ("hmassPos", "0 < mass", "sorry", "admit", "axiom ",
                      "PhysicalEndpointWeights_le_ownerWeight", "1 + Real.exp rho"):
        if forbidden in code:
            raise AssertionError(f"H4D_FORBIDDEN={forbidden}")
    for marker in (
        "cmp116CMP89PhysicalNearestEndpointOwnerDistance",
        "min\n    (finBoxDist",
        "cmp116BondTarget b", "cmp116BondSource b",
        "finTorusDist_le_natAbs_of_intCast_eq_sub",
        "finBoxDist_le_latticeL1_of_intCast_eq_siteSub",
        "selectedL1_add_boundary_of_cast",
        "Weight_le_ownerWeight_of_cast",
        "cmp116CMP89PhysicalBondFirstEndpointDisplacement_cast",
        "cmp89Eq249NearestEndpointTransport",
        "cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary",
        "norm_cmp89Eq249NormalizedCompleteHolderIntegral_le_nearestSignedL1",
    ):
        if marker not in code:
            raise AssertionError(f"H4D_MARKER_MISSING={marker}")
    if code.count("cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary") < 2:
        raise AssertionError("H4D_BOTH_ENDPOINT_OWNER_COMPARISONS_REQUIRED")

def build_payload():
    if shared.sha256(Path(shared.__file__).read_bytes()) != SHARED_SHA256:
        raise AssertionError("SHARED_HELPER_DRIFT")
    rows, inputs = [], {}
    for draft, expected, target, count, audit in INPUTS:
        content = shared.promote(shared.read_pinned(draft, expected), count, audit)
        rows.append((target, content)); inputs[draft.name] = expected
    require_semantics(rows[0][1].decode())
    records = [{"path": p.as_posix(), "sha256": shared.sha256(b), "bytes": len(b)} for p,b in rows]
    payload = {
        "status":"PRE-VALIDATION", "compiler_verified":False,
        "scope":"H4d selected physical endpoint to two-point CMP99 owner minimum",
        "positive_mass_premise":"ABSENT", "endpoint_bounds_summed":False,
        "target_only_owner_metric":False, "first_endpoint_integer_lift":"EXPLICIT",
        "boundary_cost":"EXPLICIT", "regional_B0":"OPEN", "window15":"OPEN",
        "terminal_fields":"OPEN", "shared_helper_sha256":SHARED_SHA256,
        "residue_lifts":"SUPPORTED_BY_EXPLICIT_CAST",
        "input_sha256":inputs, "files":records, "declarations":9, "axiom_prints":9,
    }
    return rows, payload

def main() -> int:
    started=time.perf_counter(); rows,payload=build_payload()
    for relative,content in rows:
        target=OVERLAY/relative; target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(content)
        if target.read_bytes()!=content: raise AssertionError(f"POST_WRITE_MISMATCH={relative.as_posix()}")
    manifest=(json.dumps(payload,indent=2,sort_keys=True)+"\n").encode(); MANIFEST.write_bytes(manifest)
    print(json.dumps({"status":"PASS","compiler_verified":False,"files":len(rows),
      "declarations":9,"axiom_prints":9,"manifest_sha256":shared.sha256(manifest),
      "elapsed_seconds":round(time.perf_counter()-started,6),"peak_rss_bytes":shared.peak_rss_bytes()},sort_keys=True))
    return 0
if __name__ == "__main__": raise SystemExit(main())
