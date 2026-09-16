#!/usr/bin/env python3
"""Fail-closed promotion of H4d two-point owner overlay."""
from __future__ import annotations
import argparse, json, subprocess
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
OVERLAY=TMP/"step8b24-c6c1-h4d-owner-transport-overlay"
MANIFEST=TMP/"STEP8B24-C6C1-H4D-OWNER-TRANSPORT-OVERLAY-MANIFEST.json"
EXPECTED_MANIFEST_SHA256="1B3A686E649F9636AD6AF613313F0EB7E1A6131A95B0280B52FDC3BE4D14B1A3"
PREREQUISITES=("BalabanCMP89Eq249NearestCompleteHolderNormalizedBound",
               "BalabanCMP99SourceLocalizationOwnerDistanceBridge")
def git(*args):
    c=subprocess.run(["git","-c","safe.directory=*",*args],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding="utf-8",check=False)
    if c.returncode: raise SystemExit("GIT_FAIL "+" ".join(args)+"\n"+c.stderr)
    return c.stdout.strip()
def require_prerequisites():
    core=(ROOT/"YangMillsCore.lean").read_text(encoding="utf-8")
    for module in PREREQUISITES:
        for suffix in (".lean","Audit.lean"):
            relative=Path("YangMills/RG")/f"{module}{suffix}"; path=ROOT/relative
            if not path.is_file(): raise SystemExit(f"H4D_PREREQUISITE_MISSING={relative.as_posix()}")
            if "PRE-VALIDATION:" in path.read_text(encoding="utf-8"): raise SystemExit(f"H4D_PREREQUISITE_NOT_SEALED={relative.as_posix()}")
        audit_import=f"import YangMills.RG.{module}Audit"
        if audit_import not in core: raise SystemExit(f"H4D_PREREQUISITE_NOT_IN_CORE={audit_import}")
def promotion_plan():
    require_prerequisites(); measured=shared.sha256(MANIFEST.read_bytes())
    if measured!=EXPECTED_MANIFEST_SHA256: raise SystemExit(f"H4D_MANIFEST_DRIFT={measured}")
    p=json.loads(MANIFEST.read_text(encoding="utf-8")); records=p["files"]
    expected={"status":"PRE-VALIDATION","compiler_verified":False,"declarations":9,"axiom_prints":9,
      "positive_mass_premise":"ABSENT","endpoint_bounds_summed":False,"target_only_owner_metric":False,
      "first_endpoint_integer_lift":"EXPLICIT","boundary_cost":"EXPLICIT","regional_B0":"OPEN",
      "window15":"OPEN","terminal_fields":"OPEN",
      "residue_lifts":"SUPPORTED_BY_EXPLICIT_CAST"}
    if any(p.get(k)!=v for k,v in expected.items()) or len(records)!=2: raise SystemExit("H4D_MANIFEST_SEMANTIC_MISMATCH")
    result=[]
    for record in records:
        relative=Path(str(record["path"])); source=OVERLAY/relative; target=ROOT/relative
        if relative.parent!=Path("YangMills/RG"): raise SystemExit(f"H4D_BAD_TARGET={relative.as_posix()}")
        if not source.is_file(): raise SystemExit(f"H4D_OVERLAY_FILE_MISSING={relative.as_posix()}")
        content=source.read_bytes()
        if shared.sha256(content)!=record["sha256"] or len(content)!=record["bytes"]: raise SystemExit(f"H4D_OVERLAY_BLOB_DRIFT={relative.as_posix()}")
        text=content.decode("utf-8")
        if text.count("PRE-VALIDATION:")!=1: raise SystemExit(f"H4D_PRE_MARKER_COUNT={relative.as_posix()}")
        if any(x in text for x in ("sorry","admit","by?","exact?")): raise SystemExit(f"H4D_FORBIDDEN_PLACEHOLDER={relative.as_posix()}")
        if target.exists(): raise SystemExit(f"H4D_TARGET_ALREADY_EXISTS={relative.as_posix()}")
        result.append((target,content))
    return result
def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--expected-head",required=True); ap.add_argument("--write",action="store_true"); a=ap.parse_args()
    actual=git("rev-parse","HEAD")
    if actual!=a.expected_head: raise SystemExit(f"HEAD_MISMATCH={actual}")
    if subprocess.run(["git","-c","safe.directory=*","diff","--quiet"],cwd=ROOT).returncode: raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(["git","-c","safe.directory=*","diff","--cached","--quiet"],cwd=ROOT).returncode: raise SystemExit("INDEX_NOT_CLEAN")
    rows=promotion_plan()
    if not a.write:
        print(f"STEP8B24_C6C1_H4D_PROMOTION_DRY_RUN_OK head={actual} new_files={len(rows)} manifest={EXPECTED_MANIFEST_SHA256}"); return 0
    for target,content in rows: target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(content)
    for target,content in rows:
        if target.read_bytes()!=content: raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(f"STEP8B24_C6C1_H4D_PROMOTION_WRITE_OK base_head={actual} new_files={len(rows)} manifest={EXPECTED_MANIFEST_SHA256}"); return 0
if __name__=="__main__": raise SystemExit(main())
