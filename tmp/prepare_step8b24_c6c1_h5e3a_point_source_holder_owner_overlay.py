#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H5e3a point-source owner overlay."""
from __future__ import annotations
import json,time
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
OVERLAY=TMP/"step8b24-c6c1-h5e3a-point-source-holder-owner-overlay"
MANIFEST=TMP/"STEP8B24-C6C1-H5E3A-POINT-SOURCE-HOLDER-OWNER-OVERLAY-MANIFEST.json"
SHARED_SHA256="D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"
INPUTS=(
 (TMP/"BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderOwnerBound.draft.lean","D8E826E4B7E0AA99E6F3DEA8DF77F97C0967067A45FF80C28A98AE7C4F6CCDBD",Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderOwnerBound.lean"),1,False),
 (TMP/"BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderOwnerBoundAudit.draft.lean","AB21AB30832BFE13A8965304360F45C42A5124B7FF68F75E7ED6654A6717863B",Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderOwnerBoundAudit.lean"),1,True),)
def require_semantics(source):
    code=shared.strip_lean_comments(source)
    for x in ("sorry","admit","axiom "):
        if x in code: raise AssertionError(f"H5E3A_FORBIDDEN={x}")
    required=(
      "cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderDifference_eq_tsumIntegral_smul",
      "tsum_norm_cmp99SourceSeparatedPhysicalHolderIntegral_le_owner",
      "summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue",
      "cmp89Eq249NormalizedFineLatticeStabilizedIntegral_physicalBond_eq_sourceCoefficient_sub_forwardCoefficient",
      "norm_tsum_le_tsum_norm", "finite cardinality")
    for x in required:
        if x not in code and x != "finite cardinality": raise AssertionError(f"H5E3A_MARKER_MISSING={x}")
    if "FinitePiLpSupportedInOwner" in code: raise AssertionError("H5E3A_SOURCE_EXTENSION_LEAK")
def build_payload():
    if shared.sha256(Path(shared.__file__).read_bytes())!=SHARED_SHA256: raise AssertionError("SHARED_HELPER_DRIFT")
    rows=[]; inputs={}
    for draft,expected,target,count,audit in INPUTS:
        content=shared.promote(shared.read_pinned(draft,expected),count,audit); rows.append((target,content)); inputs[draft.name]=expected
    require_semantics(rows[0][1].decode())
    records=[{"path":p.as_posix(),"sha256":shared.sha256(b),"bytes":len(b)} for p,b in rows]
    return rows,{"status":"PRE-VALIDATION","compiler_verified":False,
      "scope":"H5e3a generated point-source Holder difference owner bound",
      "point_source_identity":"CONSUMED","absolute_summability":"PROVED_INTERNALLY",
      "residue_owner_bound":"CONSUMED","source_extension":"OPEN","fine_cardinality":"ABSENT",
      "regional_B0":"OPEN","window15":"OPEN","terminal_fields":"OPEN",
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
