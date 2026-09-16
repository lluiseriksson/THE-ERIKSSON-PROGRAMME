#!/usr/bin/env python3
from __future__ import annotations
import json,time
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"; OVERLAY=TMP/"step8b24-c6c1-h5e1-carrier-dictionary-overlay"; MANIFEST=TMP/"STEP8B24-C6C1-H5E1-CARRIER-DICTIONARY-OVERLAY-MANIFEST.json"
SHARED="D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A"
INPUTS=((TMP/"BalabanCMP99SourceSeparatedPhysicalHolderCarrierDictionary.draft.lean","31BD90EF4C1798FD2DB5380E9CB6A3CE4C5DDCC23673C88791B5A8F3480C4E0F",Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderCarrierDictionary.lean"),5,False),(TMP/"BalabanCMP99SourceSeparatedPhysicalHolderCarrierDictionaryAudit.draft.lean","E33884A7DD491AB0F1CF15D9B09B7104E391ED91A32DF4E0593D31D81F3B8553",Path("YangMills/RG/BalabanCMP99SourceSeparatedPhysicalHolderCarrierDictionaryAudit.lean"),5,True))
def semantics(s):
    c=shared.strip_lean_comments(s)
    for x in ("sorry","admit","axiom "):
        if x in c: raise AssertionError(f"H5E1_FORBIDDEN={x}")
    for x in ("cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier","Equiv.apply_symm_apply","blockSite_blockBasepoint","cmp116BondTarget","finBoxEquivCast_shift"):
        if x not in c: raise AssertionError(f"H5E1_MISSING={x}")
def build_payload():
    if shared.sha256(Path(shared.__file__).read_bytes())!=SHARED: raise AssertionError("SHARED_HELPER_DRIFT")
    rows=[]; ins={}
    for d,h,t,n,a in INPUTS:
        b=shared.promote(shared.read_pinned(d,h),n,a); rows.append((t,b)); ins[d.name]=h
    semantics(rows[0][1].decode()); rec=[{"path":p.as_posix(),"sha256":shared.sha256(b),"bytes":len(b)} for p,b in rows]
    return rows,{"status":"PRE-VALIDATION","compiler_verified":False,"scope":"H5e1 D4-to-separated carrier, shift, bond target and owner dictionary","carrier_equality":"PROPOSITIONAL","shift_preserved":"THEOREM","owner_block_basepoint":"EXACT","metric_bound":"OPEN","regional_B0":"OPEN","window15":"OPEN","terminal_fields":"OPEN","shared_helper_sha256":SHARED,"input_sha256":ins,"files":rec,"declarations":5,"axiom_prints":5}
def main():
    t=time.perf_counter(); rows,p=build_payload()
    for rel,b in rows:
        q=OVERLAY/rel; q.parent.mkdir(parents=True,exist_ok=True); q.write_bytes(b)
        if q.read_bytes()!=b: raise AssertionError("POST_WRITE_MISMATCH")
    blob=(json.dumps(p,indent=2,sort_keys=True)+"\n").encode(); MANIFEST.write_bytes(blob)
    print(json.dumps({"status":"PASS","compiler_verified":False,"files":2,"declarations":5,"axiom_prints":5,"manifest_sha256":shared.sha256(blob),"elapsed_seconds":round(time.perf_counter()-t,6),"peak_rss_bytes":shared.peak_rss_bytes()},sort_keys=True)); return 0
if __name__=="__main__": raise SystemExit(main())
