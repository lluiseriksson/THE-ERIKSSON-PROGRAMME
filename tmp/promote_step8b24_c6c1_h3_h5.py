#!/usr/bin/env python3
"""Fail-closed batch promotion of the exact Step-8b.24 H3--H5 DAG."""
from __future__ import annotations
import argparse,hashlib,json,re,subprocess
from pathlib import Path
import audit_step8b24_c6c1_h3_h5_schedule as schedule

ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
SCHEDULE_SHA256="F604359A160B6B8E6B0142182F52A0C70A8ABEA2CFDDBF707707DA310F5EDFD7"
PENDING_EXTERNAL=(
 "YangMills.RG.BalabanCMP89CenteredGreenFourierSummability",
 "YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy",
 "YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope",
 "YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderStabilizedBound",
 "YangMills.RG.BalabanCMP89Eq249PhysicalFineHolderPhaseQuotient",
 "YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary",
 "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization",
 "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift",
 "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0",
 "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative",
)
def sha(data:bytes)->str:return hashlib.sha256(data).hexdigest().upper()
def git(*args):
    p=subprocess.run(["git","-c","safe.directory=*",*args],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding="utf-8",check=False)
    if p.returncode: raise SystemExit("GIT_FAIL "+p.stderr)
    return p.stdout.strip()
def rel_of_module(module:str)->Path:return Path(*module.split(".")).with_suffix(".lean")
def plan():
    if sha((TMP/"audit_step8b24_c6c1_h3_h5_schedule.py").read_bytes())!=SCHEDULE_SHA256:
        raise SystemExit("H3_H5_SCHEDULE_SCRIPT_DRIFT")
    core=(ROOT/"YangMillsCore.lean").read_text(encoding="utf-8")
    for module in PENDING_EXTERNAL:
        rel=rel_of_module(module); source=ROOT/rel
        audit=source.with_name(source.stem+"Audit.lean")
        if not source.is_file(): raise SystemExit(f"H3_H5_EXTERNAL_MISSING={rel.as_posix()}")
        if not audit.is_file(): raise SystemExit(f"H3_H5_EXTERNAL_AUDIT_MISSING={audit.relative_to(ROOT).as_posix()}")
        if "PRE-VALIDATION:" in source.read_text(encoding="utf-8") or "PRE-VALIDATION:" in audit.read_text(encoding="utf-8"):
            raise SystemExit(f"H3_H5_EXTERNAL_NOT_SEALED={module}")
        audit_module=module+"Audit"
        if f"import {audit_module}" not in core: raise SystemExit(f"H3_H5_EXTERNAL_NOT_IN_CORE={audit_module}")
    rows=[]; all_modules=set(); payloads=[]
    for name,overlay_name,manifest_name,expected_hash in schedule.BRICKS:
        mp=TMP/manifest_name; raw=mp.read_bytes()
        if sha(raw)!=expected_hash: raise SystemExit(f"H3_H5_MANIFEST_DRIFT={name}/{sha(raw)}")
        payload=json.loads(raw); payloads.append(payload)
        overlay=TMP/overlay_name
        for record in payload["files"]:
            rel=Path(str(record["path"])); src=overlay/rel; data=src.read_bytes()
            if sha(data)!=record["sha256"] or len(data)!=record["bytes"]: raise SystemExit(f"H3_H5_BLOB_DRIFT={name}/{rel.as_posix()}")
            if data.decode("utf-8").count("PRE-VALIDATION:")!=1: raise SystemExit(f"H3_H5_PRE_MARKER_COUNT={name}/{rel.as_posix()}")
            dst=ROOT/rel
            if dst.exists(): raise SystemExit(f"H3_H5_TARGET_ALREADY_EXISTS={rel.as_posix()}")
            rows.append((dst,data)); all_modules.add(schedule.module_of(rel.as_posix()))
    unresolved=set()
    for _,data in rows:
        for module in schedule.IMPORT_RE.findall(data.decode("utf-8")):
            if module not in all_modules and not (ROOT/rel_of_module(module)).is_file(): unresolved.add(module)
    if unresolved: raise SystemExit("H3_H5_UNRESOLVED_EXTERNAL="+",".join(sorted(unresolved)))
    if len(rows)!=38 or len({dst for dst,_ in rows})!=38: raise SystemExit(f"H3_H5_SCOPE_COUNT={len(rows)}")
    if sum(int(p["declarations"]) for p in payloads)!=65 or sum(int(p["axiom_prints"]) for p in payloads)!=60:
        raise SystemExit("H3_H5_SEMANTIC_COUNT_DRIFT")
    return rows
def main():
    parser=argparse.ArgumentParser(); parser.add_argument("--expected-head",required=True); parser.add_argument("--write",action="store_true"); args=parser.parse_args()
    head=git("rev-parse","HEAD")
    if head!=args.expected_head: raise SystemExit(f"HEAD_MISMATCH={head}")
    if subprocess.run(["git","-c","safe.directory=*","diff","--quiet"],cwd=ROOT).returncode: raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(["git","-c","safe.directory=*","diff","--cached","--quiet"],cwd=ROOT).returncode: raise SystemExit("INDEX_NOT_CLEAN")
    rows=plan()
    if not args.write:
        print(f"STEP8B24_H3_H5_BATCH_PROMOTION_DRY_RUN_OK head={head} files={len(rows)} bricks={len(schedule.BRICKS)} declarations=65 axiom_prints=60"); return 0
    for dst,data in rows: dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(data)
    for dst,data in rows:
        if dst.read_bytes()!=data: raise SystemExit(f"H3_H5_POST_WRITE_MISMATCH={dst.relative_to(ROOT).as_posix()}")
    print(f"STEP8B24_H3_H5_BATCH_PROMOTION_WRITE_OK base_head={head} files={len(rows)} bricks={len(schedule.BRICKS)} declarations=65 axiom_prints=60"); return 0
if __name__=="__main__": raise SystemExit(main())
