#!/usr/bin/env python3
"""Generate the Step-8b.24 H3--H5 restartable validation runner."""
from __future__ import annotations
import argparse,hashlib,json,re,subprocess
from pathlib import Path
import audit_step8b24_c6c1_h3_h5_schedule as schedule

ROOT=Path(__file__).resolve().parents[1]; TMP=ROOT/"tmp"
BASE_RUNNER_URL=("https://raw.githubusercontent.com/lluiseriksson/"
 "THE-ERIKSSON-PROGRAMME/bcc852cee5e709bff91fad7de26fa21cff754e1f/"
 "scripts/colab_qprime_row_validation.py")
BASE_RUNNER_SHA256="d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
BRICKS:tuple[tuple[str,int],...]=(
 ("BalabanCMP89Eq249FineLatticeCompleteHolderPeriodicity",7),
 ("BalabanCMP89Eq251CompleteHolderMassUniformHolomorphy",2),
 ("BalabanCMP89Eq251CompleteHolderMassUniformOneCoordinateContourShift",1),
 ("BalabanCMP89Eq249CompleteHolderMassUniformProductContourTelescope",5),
 ("BalabanCMP89Eq249CompleteHolderMassUniformNormalizedIntegralBound",1),
 ("BalabanCMP89Eq249CompleteHolderEndpointSwap",7),
 ("BalabanCMP89Eq249NearestCompleteHolderNormalizedBound",1),
 ("BalabanCMP116CMP89PhysicalNearestEndpointOwnerTransport",9),
 ("BalabanCMP89Eq249MassUniformRealSliceRecombination",1),
 ("BalabanCMP99SourceSeparatedPhysicalHolderTermwiseBridge",2),
 ("BalabanCMP89Eq249PhysicalHolderAlphaFactorization",4),
 ("BalabanCMP89Eq249PhysicalHolderNormalizedIntegral",3),
 ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalHolderTsum",2),
 ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolder",3),
 ("BalabanCMP99SourceSeparatedPhysicalHolderResidueOwnerProjection",3),
 ("BalabanCMP99SourceSeparatedPhysicalHolderCarrierDictionary",5),
 ("BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBound",1),
 ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderOwnerBound",1),
 ("BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldHolderOwnerBound",2),
)
def git(*args,binary=False):
    p=subprocess.run(["git","-c","safe.directory=*",*args],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    if p.returncode: raise SystemExit("GIT_FAIL "+" ".join(args)+"\n"+p.stderr.decode(errors="replace"))
    return p.stdout if binary else p.stdout.decode().strip()
def pair_paths(module):
    stem=f"YangMills/RG/{module}"; return stem+".lean",stem+"Audit.lean"
def source_paths():
    paths=[p for module,_ in BRICKS for p in pair_paths(module)]
    if len(paths)!=38 or len(set(paths))!=38: raise RuntimeError("H3_H5_SCOPE_MISMATCH")
    return paths
def static_check():
    measured=[]
    for _,overlay_name,manifest_name,_ in schedule.BRICKS:
        payload=json.loads((TMP/manifest_name).read_text(encoding="utf-8")); overlay=TMP/overlay_name
        for record in payload["files"]:
            path=str(record["path"])
            if path.endswith("Audit.lean"):
                module=Path(path).name.removesuffix("Audit.lean")
                text=(overlay/path).read_text(encoding="utf-8")
                measured.append((module,len(re.findall(r"(?m)^#print axioms ",text))))
    if tuple(measured)!=BRICKS: raise SystemExit("H3_H5_RUNNER_BRICK_SCOPE_DRIFT")
    if sum(c for _,c in BRICKS)!=60: raise SystemExit("H3_H5_AXIOM_TOTAL_DRIFT")
    print("STEP8B24_H3_H5_RUNNER_GENERATOR_STATIC_OK files=38 bricks=19 stages=38 axiom_blocks=60")
def q(x):return repr(x)
def generate(source_sha):
    if git("rev-parse",f"{source_sha}^{{commit}}")!=source_sha: raise SystemExit("SOURCE_SHA_NOT_FULL_OR_MISMATCH")
    rows=[]
    for path in source_paths():
        data=git("cat-file","blob",f"{source_sha}:{path}",binary=True); text=data.decode()
        if text.count("PRE-VALIDATION:")!=1: raise SystemExit(f"H3_H5_PRE_MARKER_COUNT={path}")
        if any(x in text for x in ("sorry","admit","by?","exact?")): raise SystemExit(f"FORBIDDEN_PLACEHOLDER={path}")
        rows.append((path,hashlib.sha256(data).hexdigest()))
    blob_rows="\n".join(f"    {q(p)}: {q(h)}," for p,h in rows)
    stages=[]
    for i,(module,count) in enumerate(BRICKS,1):
        slug=module.removeprefix("Balaban").lower()
        stages.append("    (\n"+f"        {q(f'{i:02d}_{slug}_focal')},\n"+f"        ['lake', 'build', {q('YangMills.RG.'+module)}],\n        None,\n    ),\n    (\n"+f"        {q(f'{i:02d}_{slug}_audit')},\n        ['lake', 'env', 'lean', "+f"{q('YangMills/RG/'+module+'Audit.lean')}],\n        {count},\n    ),")
    queue="\n".join(stages)
    return f'''#!/usr/bin/env python3
"""Colab gate for Step-8b.24 H3--H5; B0, window 15 and terminals remain open."""
from __future__ import annotations
import hashlib,importlib.util
from pathlib import Path
import urllib.request
HERE=Path("/content"); BASE_RUNNER=HERE/"colab_qprime_row_validation.py"
BASE_RUNNER_URL={q(BASE_RUNNER_URL)}; BASE_RUNNER_SHA256={q(BASE_RUNNER_SHA256)}
with urllib.request.urlopen(BASE_RUNNER_URL) as response: base_runner_source=response.read()
base_runner_hash=hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256="+base_runner_hash,flush=True)
if base_runner_hash!=BASE_RUNNER_SHA256: raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec=importlib.util.spec_from_file_location("step8b24_h3_h5_base_runner",BASE_RUNNER)
if spec is None or spec.loader is None: raise RuntimeError(f"cannot load base runner: {{BASE_RUNNER}}")
runner=importlib.util.module_from_spec(spec); spec.loader.exec_module(runner)
runner.RUNNER_REV="step8b24-h3-h5-v1"; runner.SOURCE_SHA={q(source_sha)}
runner.ROOT=Path("/content/hrpoly-step8b24-h3-h5")
runner.EVIDENCE=Path("/content/hrpoly-step8b24-h3-h5-evidence")
runner.ARCHIVE=Path("/content/hrpoly-step8b24-h3-h5-evidence.tar.gz")
runner.PATH_MANIFEST=Path("/content/hrpoly-step8b24-h3-h5-paths.txt")
runner.SOURCE_BLOBS={{
{blob_rows}
}}
runner.QUEUE=[
{queue}
]
if __name__=="__main__":
    try:
        from google.colab import runtime
        runtime.unassign=lambda:print("RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1",flush=True)
    except ImportError: pass
    raise SystemExit(runner.main())
'''
def main():
    p=argparse.ArgumentParser(); p.add_argument("--static-check",action="store_true"); p.add_argument("--source-sha"); p.add_argument("--output",type=Path,default=ROOT/"scripts"/"colab_step8b24_h3_h5_validation.py"); a=p.parse_args()
    if a.static_check: static_check()
    if not a.source_sha:
        if a.static_check:return 0
        raise SystemExit("SOURCE_SHA_REQUIRED")
    content=generate(a.source_sha); a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(content,encoding="utf-8",newline="\n")
    print(f"STEP8B24_H3_H5_RUNNER_GENERATED source_sha={a.source_sha} files=38 bricks=19 stages=38 axiom_blocks=60 sha256={hashlib.sha256(content.encode()).hexdigest().upper()} output={a.output}"); return 0
if __name__=="__main__":raise SystemExit(main())
