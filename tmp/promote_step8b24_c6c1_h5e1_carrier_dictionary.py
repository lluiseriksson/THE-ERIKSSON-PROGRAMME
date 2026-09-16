#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,subprocess
from pathlib import Path
import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared
ROOT=Path(__file__).resolve().parents[1];TMP=ROOT/"tmp";OVERLAY=TMP/"step8b24-c6c1-h5e1-carrier-dictionary-overlay";MANIFEST=TMP/"STEP8B24-C6C1-H5E1-CARRIER-DICTIONARY-OVERLAY-MANIFEST.json";EXPECTED="F6C7A460F696CEF6441C18395858E705ACFCF0149DBEBC9EACA44DDD70891AE5"
PREREQS=("BalabanCMP99SourceLocalizationOwnerDistanceBridge","BalabanCMP116CMP89PhysicalBondDisplacementDictionary")
def git(*a):
 c=subprocess.run(["git","-c","safe.directory=*",*a],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding="utf-8",check=False)
 if c.returncode:raise SystemExit("GIT_FAIL "+c.stderr)
 return c.stdout.strip()
def plan():
 core=(ROOT/"YangMillsCore.lean").read_text(encoding="utf-8")
 for m in PREREQS:
  for s in (".lean","Audit.lean"):
   r=Path("YangMills/RG")/f"{m}{s}";p=ROOT/r
   if not p.is_file():raise SystemExit(f"H5E1_PREREQUISITE_MISSING={r.as_posix()}")
   if "PRE-VALIDATION:" in p.read_text(encoding="utf-8"):raise SystemExit(f"H5E1_PREREQUISITE_NOT_SEALED={r.as_posix()}")
  if f"import YangMills.RG.{m}Audit" not in core:raise SystemExit(f"H5E1_PREREQUISITE_NOT_IN_CORE={m}")
 if shared.sha256(MANIFEST.read_bytes())!=EXPECTED:raise SystemExit("H5E1_MANIFEST_DRIFT")
 p=json.loads(MANIFEST.read_text(encoding="utf-8"));rs=p["files"]
 ex={"status":"PRE-VALIDATION","compiler_verified":False,"declarations":5,"axiom_prints":5,"carrier_equality":"PROPOSITIONAL","shift_preserved":"THEOREM","owner_block_basepoint":"EXACT","metric_bound":"OPEN","regional_B0":"OPEN","window15":"OPEN","terminal_fields":"OPEN"}
 if any(p.get(k)!=v for k,v in ex.items()) or len(rs)!=2:raise SystemExit("H5E1_MANIFEST_SEMANTIC_MISMATCH")
 out=[]
 for r in rs:
  rel=Path(str(r["path"]));src=OVERLAY/rel;dst=ROOT/rel
  if rel.parent!=Path("YangMills/RG") or not src.is_file():raise SystemExit(f"H5E1_BAD_FILE={rel.as_posix()}")
  b=src.read_bytes();txt=b.decode("utf-8")
  if shared.sha256(b)!=r["sha256"] or len(b)!=r["bytes"]:raise SystemExit(f"H5E1_BLOB_DRIFT={rel.as_posix()}")
  if txt.count("PRE-VALIDATION:")!=1 or any(x in txt for x in ("sorry","admit","by?","exact?")):raise SystemExit(f"H5E1_MARKER_OR_PLACEHOLDER={rel.as_posix()}")
  if dst.exists():raise SystemExit(f"H5E1_TARGET_EXISTS={rel.as_posix()}")
  out.append((dst,b))
 return out
def main():
 a=argparse.ArgumentParser();a.add_argument("--expected-head",required=True);a.add_argument("--write",action="store_true");q=a.parse_args();head=git("rev-parse","HEAD")
 if head!=q.expected_head:raise SystemExit(f"HEAD_MISMATCH={head}")
 if subprocess.run(["git","-c","safe.directory=*","diff","--quiet"],cwd=ROOT).returncode:raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
 if subprocess.run(["git","-c","safe.directory=*","diff","--cached","--quiet"],cwd=ROOT).returncode:raise SystemExit("INDEX_NOT_CLEAN")
 rows=plan()
 if not q.write:print(f"STEP8B24_C6C1_H5E1_PROMOTION_DRY_RUN_OK head={head} new_files={len(rows)} manifest={EXPECTED}");return 0
 for d,b in rows:d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b)
 for d,b in rows:
  if d.read_bytes()!=b:raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={d.relative_to(ROOT)}")
 print(f"STEP8B24_C6C1_H5E1_PROMOTION_WRITE_OK base_head={head} new_files={len(rows)} manifest={EXPECTED}");return 0
if __name__=="__main__":raise SystemExit(main())
