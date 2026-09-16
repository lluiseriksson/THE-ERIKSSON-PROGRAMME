#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H5e2 residue-family owner overlay."""
from __future__ import annotations
import json,time
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
OVERLAY=TMP/"step8b24-c6c1-h5e2-residue-family-owner-bound-overlay"
MANIFEST=TMP/"STEP8B24-C6C1-H5E2-RESIDUE-FAMILY-OWNER-BOUND-OVERLAY-MANIFEST.json"
SHARED_SHA256="D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"
INPUTS=(
 (TMP/"BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBound.draft.lean","D210EA5BB44695B7A3D1C5E31D9A01D0076A2E75A5F532BE8043F7A89F1D5AE3",Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBound.lean"),1,False),
 (TMP/"BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBoundAudit.draft.lean","CB8ED17FA5CC9E4F72FCC03B5E1DA505D8A7689746537F8AB36EDA73D6FC1F2F",Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBoundAudit.lean"),1,True),)
def require_semantics(source):
    code=shared.strip_lean_comments(source)
    for x in ("sorry","admit","axiom "):
        if x in code: raise AssertionError(f"H5E2_FORBIDDEN={x}")
    required=("tsum_norm_cmp99FlatIntegerZeroResidueClass_le_centeredPeriodic",
      "cmp99SourceSeparatedPhysicalHolderCenteredForwardBase_cast_eq_target_sub_blockBasepoint",
      "cmp116CMP89PhysicalNearestEndpointWeight_le_ownerWeight_of_cast",
      "cmp89Eq251LatticeL1Length_nearestEndpointTransport_eq_min",
      "min_le_left", "fine cardinality")
    for x in required:
        if x not in code and x != "fine cardinality": raise AssertionError(f"H5E2_MARKER_MISSING={x}")
    if "rho / 2" in code or "rho / (2" in code: raise AssertionError("H5E2_RATE_SPLIT")
def build_payload():
    if shared.sha256(Path(shared.__file__).read_bytes())!=SHARED_SHA256: raise AssertionError("SHARED_HELPER_DRIFT")
    rows=[]; inputs={}
    for draft,expected,target,count,audit in INPUTS:
        content=shared.promote(shared.read_pinned(draft,expected),count,audit); rows.append((target,content)); inputs[draft.name]=expected
    require_semantics(rows[0][1].decode())
    records=[{"path":p.as_posix(),"sha256":shared.sha256(b),"bytes":len(b)} for p,b in rows]
    return rows,{"status":"PRE-VALIDATION","compiler_verified":False,
      "scope":"H5e2 exact zero-residue family to centered two-point owner bound",
      "zero_residue_family":"CONSUMED","centered_residual_projection":"CONSUMED",
      "carrier_transport":"CONSUMED","rate_split":"FORBIDDEN","representative_prefactor":"ABSENT",
      "fine_cardinality":"ABSENT","regional_B0":"OPEN","window15":"OPEN","terminal_fields":"OPEN",
      "shared_helper_sha256":SHARED_SHA256,"input_sha256":inputs,"files":records,"declarations":1,"axiom_prints":1}
def main():
    t=time.perf_counter(); rows,p=build_payload()
    for rel,b in rows:
        out=OVERLAY/rel; out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(b)
        if out.read_bytes()!=b: raise AssertionError(f"POST_WRITE_MISMATCH={rel.as_posix()}")
    blob=(json.dumps(p,indent=2,sort_keys=True)+"\n").encode(); MANIFEST.write_bytes(blob)
    print(json.dumps({"status":"PASS","compiler_verified":False,"files":2,"declarations":1,"axiom_prints":1,
      "manifest_sha256":shared.sha256(blob),"elapsed_seconds":round(time.perf_counter()-t,6),"peak_rss_bytes":shared.peak_rss_bytes()},sort_keys=True)); return 0
if __name__=="__main__": raise SystemExit(main())
