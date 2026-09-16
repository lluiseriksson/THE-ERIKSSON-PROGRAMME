#!/usr/bin/env python3
"""Prepare deterministic PRE-VALIDATION H5e3b localized-field overlay."""
from __future__ import annotations
import json,time
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
OVERLAY=TMP/"step8b24-c6c1-h5e3b-localized-field-holder-owner-overlay"
MANIFEST=TMP/"STEP8B24-C6C1-H5E3B-LOCALIZED-FIELD-HOLDER-OWNER-OVERLAY-MANIFEST.json"
SHARED_SHA256="D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"
INPUTS=(
 (TMP/"BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldHolderOwnerBound.draft.lean","E07BB8D1656734F87AEC9F6F08E26D3360A036AACC04EAD6413F86C2D1B49D51",Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldHolderOwnerBound.lean"),2,False),
 (TMP/"BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldHolderOwnerBoundAudit.draft.lean","90F774C5C8196817D2A203077C798FE991C4F76CBF6749E7D989088CF9C58FDD",Path("YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldHolderOwnerBoundAudit.lean"),2,True),)
def require_semantics(source):
    code=shared.strip_lean_comments(source)
    for x in ("sorry","admit","axiom "):
        if x in code: raise AssertionError(f"H5E3B_FORBIDDEN={x}")
    required=("def cmp99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldDerivative",
      "FinitePiLpSupportedInOwner (fun y => y)",
      "finitePiLp_of_supportedInIdentityOwner_eq_flatComplexFibrePointSource",
      "norm_cmp99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderDifference_le_owner",
      "norm_apply_le_finitePiLpSupNorm", "finitePiLpSupNorm f",
      "unfold cmp99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldDerivative")
    for x in required:
        if x not in code: raise AssertionError(f"H5E3B_MARKER_MISSING={x}")
    if ".card" in code or "Fintype.card" in code: raise AssertionError("H5E3B_CARDINALITY_LEAK")
def build_payload():
    if shared.sha256(Path(shared.__file__).read_bytes())!=SHARED_SHA256: raise AssertionError("SHARED_HELPER_DRIFT")
    rows=[]; inputs={}
    for draft,expected,target,count,audit in INPUTS:
        content=shared.promote(shared.read_pinned(draft,expected),count,audit); rows.append((target,content)); inputs[draft.name]=expected
    require_semantics(rows[0][1].decode())
    records=[{"path":p.as_posix(),"sha256":shared.sha256(b),"bytes":len(b)} for p,b in rows]
    return rows,{"status":"PRE-VALIDATION","compiler_verified":False,
      "scope":"H5e3b localized identity-owner field Holder bound",
      "point_source_owner_bound":"CONSUMED","identity_owner_reduction":"CONSUMED",
      "source_norm":"FINITE_SUP","owner_fibre_cardinality":"ABSENT","fine_cardinality":"ABSENT",
      "regional_B0":"OPEN","window15":"OPEN","terminal_fields":"OPEN",
      "shared_helper_sha256":SHARED_SHA256,"input_sha256":inputs,"files":records,"declarations":2,"axiom_prints":2}
def main():
    t=time.perf_counter(); rows,p=build_payload()
    for rel,b in rows:
        out=OVERLAY/rel; out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(b)
        if out.read_bytes()!=b: raise AssertionError(f"POST_WRITE_MISMATCH={rel.as_posix()}")
    blob=(json.dumps(p,indent=2,sort_keys=True)+"\n").encode(); MANIFEST.write_bytes(blob)
    print(json.dumps({"status":"PASS","compiler_verified":False,"files":2,"declarations":2,"axiom_prints":2,
      "manifest_sha256":shared.sha256(blob),"elapsed_seconds":round(time.perf_counter()-t,6),"peak_rss_bytes":shared.peak_rss_bytes()},sort_keys=True)); return 0
if __name__=="__main__": raise SystemExit(main())
