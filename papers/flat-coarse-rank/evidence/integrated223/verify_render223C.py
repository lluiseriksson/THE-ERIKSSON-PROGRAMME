from pathlib import Path
import json,hashlib,zipfile,shutil,datetime
A=Path(r'D:\Datos\the-eriksson-programme\autonomia');E=A/'evidencia-223';D=Path(r'D:\Entregas\the-eriksson-programme\2026-11-09_integrated223');R=D/'attempt-c';O=D/'exact223C'
def require(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['allocation','execution','download','release']:require((R/(name+'223.exit')).read_text().strip()=='0','Actual lifecycle '+name)
z=R/'tep223C-review.zip';require(not O.exists(),'Never overwrite render history');O.mkdir()
with zipfile.ZipFile(z) as arc:
 require(len(arc.namelist())==len(set(arc.namelist())),'Duplicate members')
 for n in arc.namelist():require(Path(n).name==n and '/' not in n and '\\' not in n and n not in ['.','..'],'Unsafe member')
 arc.extractall(O)
manifest=json.loads((O/'manifest.json').read_text(encoding='utf-8'))
for x in manifest:require((O/x['path']).stat().st_size==x['bytes'] and sha(O/x['path'])==x['sha256'],'Exact manifest member '+x['path'])
r=json.loads((O/'report.json').read_text(encoding='utf-8'));require(r['status']=='RENDERED_PENDING_VISUAL_REVIEW','Failed report must stay failed');require(r['source_sha']=='ddd2cf605c1715a03d2e87991e920c0ec760e527','Frozen sourceC');require(len(r['source_inputs'])==13,'Frozen13inputs')
require(len(r['tool_exits'])==10 and all(v==0 for v in r['tool_exits'].values()),'Ten actual render tools');require(r['layout_warnings']==[],'Exact final layout warnings')
pdf=O/'flat_critical_integrated.pdf';require(sha(pdf)==r['pdf_sha256'] and pdf.stat().st_size==r['pdf_bytes'],'Exact PDF')
shutil.copyfile(pdf,D/'flat_critical_integrated223C.pdf');images=Path(r'D:\Capturas\the-eriksson-programme\2026-11-10_integrated223-c');images.mkdir(exist_ok=True)
for p in O.glob('contact-*.jpg'):shutil.copyfile(p,images/p.name)
require((E/'runtime223C-backend-readback.exit').read_text().strip()=='0' and 'No active sessions found on server.' in (E/'runtime223C-backend-readback.txt').read_text(),'Separate inactive backend readback')
out={'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha':r['source_sha'],'archive_sha256':sha(z),'archive_bytes':z.stat().st_size,'manifest_members_verified':len(manifest),'report':r,'visual_review':'PENDING','numerical_exact_PDF_assessment':'NOT_YET_REQUESTED','formal_or_scientific_replay':False,'all_original_A_B_archives_preserved':True,'runtime_open_request':(R/'runtime223-open-requested.txt').read_text().strip(),'runtime_release_finished':(R/'runtime223-release-finished.txt').read_text().strip(),'backend_readback':(E/'runtime223C-backend-readback.txt').read_text().strip(),'shared_runtime':False,'billed_compute_units':None}
(E/'archive223C-verified.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');shutil.copyfile(__file__,E/'verify_render223C.py');print(json.dumps({'source':r['source_sha'],'pages':r['pages'],'pdf_sha256':r['pdf_sha256'],'pdf_bytes':r['pdf_bytes'],'all_manifest_members_verified':len(manifest),'warnings':r['layout_warnings'],'runtime':'INACTIVE','visual_and_numerical_review':'PENDING'}))
