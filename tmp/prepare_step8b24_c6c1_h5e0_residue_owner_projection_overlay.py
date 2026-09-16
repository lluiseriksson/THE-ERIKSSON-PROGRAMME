#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H5e0 residue projection overlay."""
from __future__ import annotations
import json,time
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
OVERLAY=TMP/"step8b24-c6c1-h5e0-residue-owner-projection-overlay"
MANIFEST=TMP/"STEP8B24-C6C1-H5E0-RESIDUE-OWNER-PROJECTION-OVERLAY-MANIFEST.json"
SHARED_SHA256="D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"
INPUTS=(
 (TMP/"BalabanCMP99SourceSeparatedPhysicalHolderResidueOwnerProjection.draft.lean","6A9671EF28C5D8BC88D5C599C644D2C3F0B04D89BD7FBA34E49E2FF405AEE29F",Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderResidueOwnerProjection.lean"),3,False),
 (TMP/"BalabanCMP99SourceSeparatedPhysicalHolderResidueOwnerProjectionAudit.draft.lean","EB2E12CF7D3ECADC2B7D1290244241520D199755E54C08C04C29D10545DE06CD",Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderResidueOwnerProjectionAudit.lean"),3,True),)
def require_semantics(source):
    code=shared.strip_lean_comments(source)
    for x in ("sorry","admit","axiom "):
        if x in code: raise AssertionError(f"H5E0_FORBIDDEN={x}")
    for x in ("cmp99SourceSeparatedFineTargetShiftResidueEquiv","cmp99SourceSeparatedFineTargetShift_affineResidue_eq_forward",
              "cmp99FlatIntegerZeroResidueClassQuotient_spec","blockBasepoint","ZMod (M * N)",
              "cmp99CenteredPeriodicEndpointVectorRepresentative",
              "cmp99CenteredPeriodicEndpointRepresentative_cast_eq"):
        if x not in code: raise AssertionError(f"H5E0_MARKER_MISSING={x}")
def build_payload():
    if shared.sha256(Path(shared.__file__).read_bytes())!=SHARED_SHA256: raise AssertionError("SHARED_HELPER_DRIFT")
    rows=[]; inputs={}
    for draft,expected,target,count,audit in INPUTS:
        content=shared.promote(shared.read_pinned(draft,expected),count,audit); rows.append((target,content)); inputs[draft.name]=expected
    require_semantics(rows[0][1].decode())
    records=[{"path":p.as_posix(),"sha256":shared.sha256(b),"bytes":len(b)} for p,b in rows]
    return rows,{"status":"PRE-VALIDATION","compiler_verified":False,
      "scope":"H5e0 zero-residue affine lift periodic endpoint projection",
      "zero_residue_quotient":"CONSUMED","target_wrap_carry":"CONSUMED",
      "centered_residual_projection":"PROVED",
      "carrier_transport":"OPEN","owner_bound":"OPEN","regional_B0":"OPEN","window15":"OPEN","terminal_fields":"OPEN",
      "shared_helper_sha256":SHARED_SHA256,"input_sha256":inputs,"files":records,"declarations":3,"axiom_prints":3}
def main():
    t=time.perf_counter(); rows,p=build_payload()
    for rel,b in rows:
        out=OVERLAY/rel; out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(b)
        if out.read_bytes()!=b: raise AssertionError(f"POST_WRITE_MISMATCH={rel.as_posix()}")
    blob=(json.dumps(p,indent=2,sort_keys=True)+"\n").encode(); MANIFEST.write_bytes(blob)
    print(json.dumps({"status":"PASS","compiler_verified":False,"files":2,"declarations":3,"axiom_prints":3,
      "manifest_sha256":shared.sha256(blob),"elapsed_seconds":round(time.perf_counter()-t,6),"peak_rss_bytes":shared.peak_rss_bytes()},sort_keys=True)); return 0
if __name__=="__main__": raise SystemExit(main())
