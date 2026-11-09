from pathlib import Path
import json,hashlib,zipfile,datetime,shutil
E=Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-222')
def require(v,m):
 if not v:raise ValueError(m)
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
zpath=E/'tep222-diagnostic.zip';out=E/'exact-run';out.mkdir(exist_ok=True)
with zipfile.ZipFile(zpath) as z:
 require(len(z.namelist())==len(set(z.namelist())),'Duplicate archive paths')
 for name in z.namelist():
  require(Path(name).name==name,'Unsafe archive member');(out/name).write_bytes(z.read(name))
manifest=read(out/'manifest222.json')
for name,digest in manifest.items():require(hashlib.sha256((out/name).read_bytes()).hexdigest()==digest,'Exact manifest member '+name)
report=read(out/'report222.json');require(report['source_sha']=='c993dff04868d01d37b6ec87e0417da3c91a1330','Actual pinned source')
require(report['status']=='FINITE_DIAGNOSTICS_CHECKED' and report['exits']=={'normal':0,'optimized':0},'Real child results')
for mode in ['normal','optimized']:require((out/(mode+'.exit')).read_text().strip()=='0','Actual child sentinel')
require((out/'normal.stdout.json').read_bytes()==(out/'optimized.stdout.json').read_bytes(),'Same exact normal/optimized stdout')
finite=read(out/'normal.stdout.json');require(finite['partitions']==200 and finite['global_fields']==800 and finite['negative_controls_rejected']==3,'Finite acceptance counters')
for name in ['allocation','execution','download','release']:require((E/(name+'222.exit')).read_text().strip()=='0','Own runtime lifecycle '+name)
require((E/'runtime222-backend-readback.exit').read_text().strip()=='0' and 'No active sessions found on server.' in (E/'runtime222-backend-readback.txt').read_text(),'Separate backend release readback')
r={'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha':report['source_sha'],'archive_sha256':hashlib.sha256(zpath.read_bytes()).hexdigest(),'archive_bytes':zpath.stat().st_size,'manifest_all_members_verified':True,'report':report,'finite_checks':finite,'runtime_type':'Own Colab CPU/high-memory tep222-own-cpu','runtime_open_requested':(E/'runtime222-open-requested.txt').read_text().strip(),'runtime_release_finished':(E/'runtime222-release-finished.txt').read_text().strip(),'runtime_backend_inactive':True,'compute_units_billed':None,'independent_two_clone_reproduction':False,'all_size_or_formal_proof':False,'original_wrong_distribution_attempt_preserved':True}
(E/'archive-verified222.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');shutil.copyfile(__file__,E/'verify_evidence222.py');print(json.dumps(r))
