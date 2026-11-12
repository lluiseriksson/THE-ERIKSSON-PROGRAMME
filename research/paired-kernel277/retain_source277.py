"""Metadata-only source preservation; no numerical program imported/executed."""
from pathlib import Path
import json,hashlib,shutil,subprocess
P=Path(__file__).resolve().parent;W=P.parents[1];D=Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-277\source-preparation')
if D.exists():raise ValueError('Preserve existing277 preparation; choose a new explicit version')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
required={'diagnostic277.py':'ba9f495125acad9f6ddd12d64564f7e966324ebc52eb8677dc4ee75427f3d984','diagnostic277B.py':'256362a3d76b4c3609d3bba9f58966ddf05776f27f1789f6a151ada99735ada5'}
for name,digest in required.items():
    if h(P/name)!=digest:raise ValueError('Frozen source changed '+name)
inputdir=W/'papers/flat-coarse-rank/research-consolidation/solenoidal275'
inputs=[]
for name in ['layer-stream275A.txt','constraints276A.txt','STATUS276.txt']:
    p=inputdir/name;inputs.append({'repository_path':p.relative_to(W).as_posix(),'raw_checkout_sha256':h(p),'bytes':p.stat().st_size})
(P/'construction-inputs.json').write_text(json.dumps({'construction_base':'801004ccd85170de6b39146decd34cc6400c2060','files':inputs,'runtime_math_executed':False},indent=2)+'\n',encoding='utf-8')
shutil.copytree(P,D)
for name in ['layer-stream275A.txt','constraints276A.txt','STATUS276.txt']:
    dest=D/'exact-read-inputs'/name;dest.parent.mkdir(exist_ok=True);shutil.copyfile(inputdir/name,dest)
rows=[{'path':p.relative_to(D).as_posix(),'bytes':p.stat().st_size,'raw_sha256':h(p)} for p in sorted(D.rglob('*')) if p.is_file()]
(D/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')
for row in rows:
    p=D/row['path']
    if p.stat().st_size!=row['bytes'] or h(p)!=row['raw_sha256']:raise ValueError('277 source copy readback differs')
print(json.dumps({'source_preparation':str(D),'source_files':len(rows),'preparation_manifest_raw_sha256':h(D/'manifest.json'),'B_raw_sha256':h(P/'diagnostic277B.py'),'runner_manifest_raw_sha256':h(P/'RUNNER-HASHES.json')},indent=2))
