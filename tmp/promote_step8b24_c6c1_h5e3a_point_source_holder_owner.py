#!/usr/bin/env python3
"""Fail-closed promotion of H5e3a point-source Holder owner overlay."""
from __future__ import annotations
import argparse,json,subprocess
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
OVERLAY=TMP/"step8b24-c6c1-h5e3a-point-source-holder-owner-overlay"
MANIFEST=TMP/"STEP8B24-C6C1-H5E3A-POINT-SOURCE-HOLDER-OWNER-OVERLAY-MANIFEST.json"
EXPECTED="5C4FA90BBD391ECB0C955CBE5BA858E286466CB57EB80C95CB31FFC2C377A1D5"
PREREQS=("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolder",
  "BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBound")
def git(*a):
    c=subprocess.run(["git","-c","safe.directory=*",*a],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding="utf-8",check=False)
    if c.returncode: raise SystemExit("GIT_FAIL "+c.stderr)
    return c.stdout.strip()
def plan():
    core=(ROOT/"YangMillsCore.lean").read_text(encoding="utf-8")
    for prereq in PREREQS:
        for s in (".lean","Audit.lean"):
            rel=Path("YangMills/RG")/f"{prereq}{s}"; p=ROOT/rel
            if not p.is_file(): raise SystemExit(f"H5E3A_PREREQUISITE_MISSING={rel.as_posix()}")
            if "PRE-VALIDATION:" in p.read_text(encoding="utf-8"): raise SystemExit(f"H5E3A_PREREQUISITE_NOT_SEALED={rel.as_posix()}")
        if f"import YangMills.RG.{prereq}Audit" not in core: raise SystemExit(f"H5E3A_PREREQUISITE_NOT_IN_CORE={prereq}")
    measured=shared.sha256(MANIFEST.read_bytes())
    if measured!=EXPECTED: raise SystemExit(f"H5E3A_MANIFEST_DRIFT={measured}")
    p=json.loads(MANIFEST.read_text(encoding="utf-8")); records=p["files"]
    expected={"status":"PRE-VALIDATION","compiler_verified":False,"declarations":1,"axiom_prints":1,
      "point_source_identity":"CONSUMED","absolute_summability":"PROVED_INTERNALLY",
      "residue_owner_bound":"CONSUMED","source_extension":"OPEN","fine_cardinality":"ABSENT",
      "regional_B0":"OPEN","window15":"OPEN","terminal_fields":"OPEN"}
    if any(p.get(k)!=v for k,v in expected.items()) or len(records)!=2: raise SystemExit("H5E3A_MANIFEST_SEMANTIC_MISMATCH")
    out=[]
    for r in records:
        rel=Path(str(r["path"])); src=OVERLAY/rel; dst=ROOT/rel
        if rel.parent!=Path("YangMills/RG") or not src.is_file(): raise SystemExit(f"H5E3A_BAD_FILE={rel.as_posix()}")
        b=src.read_bytes()
        if shared.sha256(b)!=r["sha256"] or len(b)!=r["bytes"]: raise SystemExit(f"H5E3A_BLOB_DRIFT={rel.as_posix()}")
        text=b.decode("utf-8")
        if text.count("PRE-VALIDATION:")!=1 or any(x in text for x in ("sorry","admit","by?","exact?")): raise SystemExit(f"H5E3A_MARKER_OR_PLACEHOLDER={rel.as_posix()}")
        if dst.exists(): raise SystemExit(f"H5E3A_TARGET_ALREADY_EXISTS={rel.as_posix()}")
        out.append((dst,b))
    return out
def main():
    a=argparse.ArgumentParser(); a.add_argument("--expected-head",required=True); a.add_argument("--write",action="store_true"); q=a.parse_args()
    head=git("rev-parse","HEAD")
    if head!=q.expected_head: raise SystemExit(f"HEAD_MISMATCH={head}")
    if subprocess.run(["git","-c","safe.directory=*","diff","--quiet"],cwd=ROOT).returncode: raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(["git","-c","safe.directory=*","diff","--cached","--quiet"],cwd=ROOT).returncode: raise SystemExit("INDEX_NOT_CLEAN")
    rows=plan()
    if not q.write: print(f"STEP8B24_C6C1_H5E3A_PROMOTION_DRY_RUN_OK head={head} new_files={len(rows)} manifest={EXPECTED}"); return 0
    for dst,b in rows: dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(b)
    for dst,b in rows:
        if dst.read_bytes()!=b: raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={dst.relative_to(ROOT)}")
    print(f"STEP8B24_C6C1_H5E3A_PROMOTION_WRITE_OK base_head={head} new_files={len(rows)} manifest={EXPECTED}"); return 0
if __name__=="__main__": raise SystemExit(main())
