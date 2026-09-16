#!/usr/bin/env python3
"""Read-only exact schedule gate for the Step-8b.24 H3--H5 overlays."""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
BRICKS=(
 ("H3ab","step8b24-c6c1-h3-mass-uniform-contour-overlay","STEP8B24-C6C1-H3-MASS-UNIFORM-CONTOUR-OVERLAY-MANIFEST.json","D887872AF1D88F8139A590FF07AC1F35F4D787C2BF984D0DDB9767F26830BC89"),
 ("H3c","step8b24-c6c1-h3c-product-telescope-overlay","STEP8B24-C6C1-H3C-PRODUCT-TELESCOPE-OVERLAY-MANIFEST.json","35A3A58C2986B5074ED9AB2023259699B3DAB981A98F90CEC6D96BA7079D3CC3"),
 ("H3d","step8b24-c6c1-h3d-normalized-bound-overlay","STEP8B24-C6C1-H3D-NORMALIZED-BOUND-OVERLAY-MANIFEST.json","84186FBFD6A1CC028F853E837AB03BF6D785C933EFF1AC201F09B59E93D9C06A"),
 ("H4ab","step8b24-c6c1-h4-swap-overlay","STEP8B24-C6C1-H4-SWAP-OVERLAY-MANIFEST.json","A8EC12904CB695C8EB1258D6FA3B6BB010BD907EBC8F39C3433E9AD5672E0DC9"),
 ("H4c","step8b24-c6c1-h4c-nearest-bound-overlay","STEP8B24-C6C1-H4C-NEAREST-BOUND-OVERLAY-MANIFEST.json","F650C9E28ACA8EDCD9C0A85C4AAAA4A0B249A43438653CFE81018FD4A01D78BE"),
 ("H4d","step8b24-c6c1-h4d-owner-transport-overlay","STEP8B24-C6C1-H4D-OWNER-TRANSPORT-OVERLAY-MANIFEST.json","1B3A686E649F9636AD6AF613313F0EB7E1A6131A95B0280B52FDC3BE4D14B1A3"),
 ("H5term","step8b24-c6c1-h5-termwise-overlay","STEP8B24-C6C1-H5-TERMWISE-OVERLAY-MANIFEST.json","826C1D7567A949FE6E212CC61E053C3009C69AF94A394144158B269782C40640"),
 ("H5factor","step8b24-c6c1-h5-holder-factor-overlay","STEP8B24-C6C1-H5-HOLDER-FACTOR-OVERLAY-MANIFEST.json","E5FCFA044FECE89BC64229D1D55DB5C2E4F2C68D752F0F38EAED4A6AFD69D2C3"),
 ("H5gen","step8b24-c6c1-h5-generated-holder-overlay","STEP8B24-C6C1-H5-GENERATED-HOLDER-OVERLAY-MANIFEST.json","3990E079577DB1272C9195AE7515FCA2B6D7B864C4020F340E941AEDDE06DFEC"),
 ("H5e0","step8b24-c6c1-h5e0-residue-owner-projection-overlay","STEP8B24-C6C1-H5E0-RESIDUE-OWNER-PROJECTION-OVERLAY-MANIFEST.json","46AC30FE60920AC8B4C158A6880FD6B73D3AF90C0866DA6A0CAFEFF0F1420DBC"),
 ("H5e1","step8b24-c6c1-h5e1-carrier-dictionary-overlay","STEP8B24-C6C1-H5E1-CARRIER-DICTIONARY-OVERLAY-MANIFEST.json","F6C7A460F696CEF6441C18395858E705ACFCF0149DBEBC9EACA44DDD70891AE5"),
 ("H5e2","step8b24-c6c1-h5e2-residue-family-owner-bound-overlay","STEP8B24-C6C1-H5E2-RESIDUE-FAMILY-OWNER-BOUND-OVERLAY-MANIFEST.json","819A26F4351FA04D3861B947584B486F54F4F83C71BC79F0F2E2B974A47FCA46"),
 ("H5e3a","step8b24-c6c1-h5e3a-point-source-holder-owner-overlay","STEP8B24-C6C1-H5E3A-POINT-SOURCE-HOLDER-OWNER-OVERLAY-MANIFEST.json","5C4FA90BBD391ECB0C955CBE5BA858E286466CB57EB80C95CB31FFC2C377A1D5"),
 ("H5e3b","step8b24-c6c1-h5e3b-localized-field-holder-owner-overlay","STEP8B24-C6C1-H5E3B-LOCALIZED-FIELD-HOLDER-OWNER-OVERLAY-MANIFEST.json","F45C97E9EB9E81E70DCDE6FDE6765CBDD6B2CDF9E20D63CF553E3116641EAED3"),
)
IMPORT_RE=re.compile(r"(?m)^import\s+([A-Za-z0-9_.']+)\s*$")
def sha(data:bytes)->str:return hashlib.sha256(data).hexdigest().upper()
def module_of(path:str)->str:return path[:-5].replace("/",".")
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--require-ready",action="store_true")
    args=parser.parse_args()
    t=time.perf_counter(); rows=[]; owner={}; total_decl=total_axiom=0
    for index,(name,overlay_name,manifest_name,expected_hash) in enumerate(BRICKS):
        mp=TMP/manifest_name; raw=mp.read_bytes()
        if sha(raw)!=expected_hash: raise SystemExit(f"MANIFEST_DRIFT={name}/{sha(raw)}")
        payload=json.loads(raw); files=payload.get("files",[])
        if payload.get("status")!="PRE-VALIDATION" or payload.get("compiler_verified") is not False:
            raise SystemExit(f"BAD_STATUS={name}")
        overlay=TMP/overlay_name
        if not files or len(files)%2: raise SystemExit(f"BAD_FILE_COUNT={name}/{len(files)}")
        total_decl+=int(payload["declarations"]); total_axiom+=int(payload["axiom_prints"])
        brick_modules=set()
        for record in files:
            path=str(record["path"])
            if path in owner: raise SystemExit(f"PATH_OVERLAP={path}/{owner[path]}/{name}")
            owner[path]=name; source=overlay/path; data=source.read_bytes()
            if sha(data)!=record["sha256"] or len(data)!=record["bytes"]:
                raise SystemExit(f"BLOB_DRIFT={name}/{path}")
            if data.decode("utf-8").count("PRE-VALIDATION:")!=1:
                raise SystemExit(f"PRE_MARKER_COUNT={name}/{path}")
            brick_modules.add(module_of(path))
            rows.append((index,name,path,data.decode("utf-8")))
        for path in (str(r["path"]) for r in files):
            if path.endswith("Audit.lean"):
                source_path=path.replace("Audit.lean",".lean")
                if source_path not in owner or owner[source_path]!=name:
                    raise SystemExit(f"PAIR_MISSING={name}/{path}")
    module_index={module_of(path):index for index,_,path,_ in rows}
    internal_edges=external_edges=0; unresolved=set()
    for index,name,path,text in rows:
        for imported in IMPORT_RE.findall(text):
            if imported in module_index:
                internal_edges+=1
                if module_index[imported]>index:
                    raise SystemExit(f"FORWARD_IMPORT={name}/{path}/{imported}")
            else:
                external_edges+=1
                rel=Path(*imported.split(".")).with_suffix(".lean")
                if not (ROOT/rel).is_file(): unresolved.add(imported)
    if args.require_ready and unresolved:
        raise SystemExit("STEP8B24_H3_H5_PROMOTION_NOT_READY="+",".join(sorted(unresolved)))
    print(f"STEP8B24_H3_H5_SCHEDULE_OK bricks={len(BRICKS)} files={len(rows)} declarations={total_decl} axiom_prints={total_axiom} internal_edges={internal_edges} external_edges={external_edges} pending_external={len(unresolved)} schedule_sha256={sha('|'.join(x[0] for x in BRICKS).encode())}")
    for index,(name,_,_,_) in enumerate(BRICKS,1): print(f"{index:02d} {name}")
    for imported in sorted(unresolved): print(f"PENDING_EXTERNAL={imported}")
    print(f"elapsed_seconds={time.perf_counter()-t:.6f}")
if __name__=="__main__": main()
