"""Metadata-only bounded bootstrap delta. Does not import/run diagnostic."""
from pathlib import Path
import json,hashlib,shutil
P=Path(__file__).resolve().parent
for name in ['launch281.py','bootstrap281-template.txt','RUNNER-HASHES.json','CONSTRUCTION281.md']:
    old=P/(name+'.defaultthreads-preserved')
    if old.exists():raise ValueError('Preserve previous delta; no rerun')
    shutil.copyfile(P/name,old)
for name in ['launch281.py','bootstrap281-template.txt']:
    s=(P/name).read_text(encoding='utf-8')
    target='p=subprocess.Popen(argv,cwd=root,stdout=out,stderr=err)'
    if s.count(target)!=1:raise ValueError('Exact bootstrap Popen source differs')
    s=s.replace(target,"p=subprocess.Popen(argv,cwd=root,stdout=out,stderr=err,env={**os.environ,'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1','MKL_NUM_THREADS':'1','NUMEXPR_NUM_THREADS':'1','VECLIB_MAXIMUM_THREADS':'1','BLIS_NUM_THREADS':'1'})")
    with (P/name).open('w',encoding='utf-8',newline='\n') as f:f.write(s)
with (P/'CONSTRUCTION281.md').open('a',encoding='utf-8',newline='\n') as f:
    f.write('\nFinal pre-execution operational delta: parent requested predictable native thread bounds. The bootstrap now supplies OMP/OPENBLAS/MKL/NUMEXPR/VECLIB/BLIS thread environment1 to each standalone child before NumPy import; the actual diagnostic records inherited OMP/OPENBLAS/MKL values and native build configuration. This requests native-library thread limits, not an observed worker-count guarantee. Exact prechange launch/template/manifest/notes bytes remain in .defaultthreads-preserved files and the first immutable D preparation packet. Numerical B bytes did not change. No numerical execution was used to make this source delta.\n')
rows=json.loads((P/'RUNNER-HASHES.json').read_bytes())
for row in rows:row['bytes']=(P/row['path']).stat().st_size;row['sha256']=hashlib.sha256((P/row['path']).read_bytes()).hexdigest()
with (P/'RUNNER-HASHES.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(rows,f,indent=2);f.write('\n')
old=Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-281\source-preparation')
D=old.with_name('source-preparation-thread-bound-final')
if D.exists():raise ValueError('Final packet exists; preserve it')
D.mkdir(parents=True,exist_ok=False);(D/'source').mkdir();shutil.copytree(old/'inputs',D/'inputs')
for p in sorted(P.iterdir()):
    if p.is_file():shutil.copyfile(p,D/'source'/p.name)
for name in ['assignment.txt','parent-pre-freeze-correction.txt']:shutil.copyfile(old/name,D/name)
ctx=json.loads((old/'context-and-subjects.json').read_bytes())
ctx['runner_manifest_sha256']=hashlib.sha256((P/'RUNNER-HASHES.json').read_bytes()).hexdigest()
ctx['metadata_preparation']='Editing, byte copying/hashing/base64 only; no diagnostic import or numerical execution. No worker pool created by metadata helpers. No unsupported timing/RSS guarantee is made.'
ctx['supersedes_for_operative_wrapper']=str(old)
ctx['prior_packet_manifest_sha256']=hashlib.sha256((old/'manifest.json').read_bytes()).hexdigest()
ctx['bootstrap_thread_policy']='Requested native thread environment1 before child imports; actual runtime thread counts unobserved, not guaranteed.'
with (D/'context-and-subjects.json').open('x',encoding='utf-8',newline='\n') as f:json.dump(ctx,f,indent=2);f.write('\n')
assignment='Parent operational correction: bootstrap/diagnostic did not set BLAS thread environment before NumPy import. Either accurately retain native default thread environment or set explicit limits before launching child and rebuild manifest, preserving prechange raw version. Parent prefers explicit1 for predictable bounded run. No mathematical source change requested; B retained.\n'
with (D/'parent-thread-correction.txt').open('x',encoding='utf-8',newline='\n') as f:f.write(assignment)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=[{'path':p.relative_to(D).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(D.rglob('*')) if p.is_file()]
with (D/'manifest.json').open('x',encoding='utf-8',newline='\n') as f:json.dump(manifest,f,indent=2);f.write('\n')
print(json.dumps({'final_packet':str(D),'manifest_members':len(manifest),'packet_manifest_sha256':sha(D/'manifest.json'),'runner_manifest_sha256':sha(P/'RUNNER-HASHES.json'),'B_source_unchanged_sha256':sha(P/'diagnostic281B.py'),'launch_sha256':sha(P/'launch281.py'),'notes_sha256':sha(P/'CONSTRUCTION281.md')},indent=2))
