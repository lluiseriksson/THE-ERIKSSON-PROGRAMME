from pathlib import Path
import json, hashlib, zipfile, os, shutil
A=Path('D:/Datos/the-eriksson-programme/autonomia'); E=A/'evidencia-228'
D=Path('D:/Entregas/the-eriksson-programme/2026-11-10_coexact-partition228')
def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(b): return hashlib.sha256(b).hexdigest()
def put(p,v):
    t=p.with_name(p.name+'.tmp'); t.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8'); os.replace(t,p)
audit=load(E/'diagnostic-source-audit-b/verdict.json')
if audit['verdict']!='accept_with_limits' or audit['blocking_findings']: raise ValueError('Source audit gate')
for x in load(E/'diagnostic-source-audit-b/hashes.json')['captures']+load(E/'diagnostic-source-audit-b/hashes.json')['outputs']:
    b=(E/'diagnostic-source-audit-b'/x['file']).read_bytes()
    if len(b)!=x['bytes'] or sha(b)!=x['sha256']: raise ValueError('Full original B audit changed')
archive=D/'attempt-b/tep228-diagnostics.zip'; out=D/'exact228B'; out.mkdir(exist_ok=True)
with zipfile.ZipFile(archive) as z:
    files=z.namelist()
    if len(files)!=10 or any('/' in n or '\\' in n for n in files): raise ValueError('Archive members')
    manifest=json.loads(z.read('MANIFEST.json'))
    if set(x['file'] for x in manifest['files'])!=set(files)-{'MANIFEST.json'}: raise ValueError('Complete payload manifest')
    for x in manifest['files']:
        b=z.read(x['file'])
        if len(b)!=x['bytes'] or sha(b)!=x['sha256']: raise ValueError(x['file'])
    report=json.loads(z.read('report.json')); data=json.loads(z.read('normal.stdout'))
    if report['status']!='FINITE_DIAGNOSTICS_CHECKED' or report['exits']!={'normal':0,'optimized':0}: raise ValueError('Actual report')
    for mode in ('normal','optimized'):
        if z.read(mode+'.exit')!=b'0\n' or z.read(mode+'.stderr'): raise ValueError('Actual child log/sentinel')
    if z.read('normal.stdout')!=z.read('optimized.stdout'): raise ValueError('Different modes')
    if data['accepted_cases']!=10 or len(data['cases'])!=10 or data['negative_controls_rejected']!=3: raise ValueError('Counters')
    keys={'wrong_codifferential_sign_rejected','one_wrong_shift_rejected','dropping_transverse_outputs_breaks_bound'}
    if set(data['negative_controls'])!=keys or any(v is not True for v in data['negative_controls'].values()): raise ValueError('Mutations')
    for name,pin in report['input_pins'].items():
        if sha(z.read(name))!=pin: raise ValueError('Source bytes')
    z.extractall(out)
record={'unit':228,'scientific_source_commit':'b0fa153f3cc2a790e659177127de27a03231a11f','archive_sha256_raw_bytes':sha(archive.read_bytes()),'archive_bytes':archive.stat().st_size,'manifest_payloads_checked':9,'actual_report':report,'selected_output':data,'source_audit':'diagnostic-source-audit-b:accept_with_limits','runtime_open_requested_utc':(D/'attempt-b/runtime228-open-requested.txt').read_text().strip(),'runtime_release_finished_utc':(D/'attempt-b/runtime228-release-finished.txt').read_text().strip(),'limits':['Ten selected exact integer matrices only; not all-size proof or full L16 coefficient-budget-family execution.','One own runtime, normal/-O are not independent clone replays.','No formal verification, novelty priority, new manuscript grade or physical gap claim.'],'scientific_execution':True,'new_paper':False,'numerical_grade':None}
for kind in ('allocation','execution','download','release'):
    if (D/('attempt-b/'+kind+'228.exit')).read_text().strip()!='0': raise ValueError('Lifecycle '+kind)
put(E/'diagnostic228B-verified.json',record);put(D/'diagnostic228B-verified.json',record)
shutil.copytree(E/'diagnostic-source-audit-b',D/'diagnostic-source-audit-b',dirs_exist_ok=True)
shutil.copyfile(__file__,E/'verify228B.py')
print(json.dumps({'verified_archive':record['archive_sha256_raw_bytes'],'selected_cases':10,'actual_mutations_rejected':3,'normal_exit':0,'optimized_exit':0,'runtime_released':True}))
