from pathlib import Path
import json,zipfile,hashlib,os,shutil,datetime
A=Path('D:/Datos/the-eriksson-programme/autonomia');E=A/'evidencia-229';D=Path('D:/Entregas/the-eriksson-programme/2026-11-10_sharp-coexact229')
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(b):return hashlib.sha256(b).hexdigest()
def put(p,v):
 t=p.with_name(p.name+'.tmp');t.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');os.replace(t,p)
prereg=load(E/'execution-preregistration229A.json');audit=load(E/'diagnostic-source-audit/verdict.json')
if audit['verdict']!='accept_with_limits' or audit['blocking_findings'] or sha((E/'diagnostic-source-audit/hashes.json').read_bytes())!=prereg['source_review_manifest_sha256']:raise ValueError('Before-execution source gate')
archive=D/'attempt-a/tep229-diagnostics.zip';out=D/'exact229A';out.mkdir(exist_ok=True)
with zipfile.ZipFile(archive) as z:
 names=z.namelist()
 if len(names)!=13 or len(set(names))!=13 or any('/' in n or '\\' in n for n in names):raise ValueError('Exact safe archive entries')
 manifest=json.loads(z.read('MANIFEST.json'))
 if {x['file'] for x in manifest['files']}!=set(names)-{'MANIFEST.json'}:raise ValueError('Complete twelve-payload manifest')
 for x in manifest['files']:
  raw=z.read(x['file'])
  if len(raw)!=x['bytes'] or sha(raw)!=x['sha256']:raise ValueError('Manifest '+x['file'])
 for name,spec in prereg['inputs'].items():
  if sha(z.read(name))!=spec['sha256']:raise ValueError('Exact source input '+name)
 report=json.loads(z.read('report.json'));data=json.loads(z.read('normal.stdout'))
 if report['status']!='FINITE_DIAGNOSTICS_CHECKED' or report['exits']!={'normal':0,'optimized':0} or report['source_context']!='source'+prereg['source_sha']:raise ValueError('Actual report gate')
 if z.read('normal.stdout')!=z.read('optimized.stdout'):raise ValueError('Actual mode outputs differ')
 dependencies={}
 for mode,flag in (('normal',0),('optimized',1)):
  if z.read(mode+'.exit')!=b'0\n' or z.read(mode+'.stderr'):raise ValueError('Actual semantic sentinel/log')
  dep=json.loads(z.read(mode+'.dependency.json'))
  if dep['actual_dependency_file']!='/content/tep229-diagnostic/coexact_partition_rank_diagnostic228.py' or dep['raw_sha256']!=prereg['inputs']['coexact_partition_rank_diagnostic228.py']['sha256'] or dep['optimization_flag']!=flag:raise ValueError('Actual dependency/mode identity')
  dependencies[mode]=dep
 if data['completed_cases']!=21 or len(data['cases'])!=21 or data['all_partitions_of_D2n2']!=15 or data['rejected_controls']!=3:raise ValueError('Completed selected counters')
 controls={'central_drift_Nyquist_kernel_rejected','omitted_constant_vector_harmonics_rejected','projected_transverse_output_class_rejected'}
 if set(data['negative_controls'])!=controls or any(x is not True for x in data['negative_controls'].values()):raise ValueError('Actual mutations')
 if len({x['partition'] for x in data['cases'][:15]})!=15 or sum(x['fibre_equality_required'] for x in data['cases'])!=3:raise ValueError('Recorded partition/fibre cases')
 z.extractall(out)
for kind in ('allocation','execution','download','release'):
 if (D/('attempt-a/'+kind+'229.exit')).read_bytes()!=b'0\n':raise ValueError('Lifecycle '+kind)
if (E/'runtime229A-backend-readback.exit').read_bytes()!=b'0\n' or 'No active sessions found on server' not in (E/'runtime229A-backend-readback.txt').read_text():raise ValueError('Separate backend inactivity readback')
r={'unit':229,'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scientific_execution_commit':prereg['source_sha'],'archive_sha256_raw_bytes':sha(archive.read_bytes()),'archive_bytes':archive.stat().st_size,'manifest_payloads_verified':12,'actual_report':report,'actual_dependency_and_modes':dependencies,'selected_output':data,'runtime_open_requested_utc':(D/'attempt-a/runtime229-open-requested.txt').read_text().strip(),'runtime_release_finished_utc':(D/'attempt-a/runtime229-release-finished.txt').read_text().strip(),'runtime_released':True,'separate_backend_no_active':True,'limits':['21selected finite cases only, no fullL16coefficient-budgetfamily or all-size executable/formal proof.','One own runtime/two optimization modes and one exact rank routine are not independent clone/algorithm reproduction.','No novelty priority, physical claim, new paper, reassessment or grade.'],'scientific_execution':True,'new_paper':False,'numerical_grade':None}
put(E/'diagnostic229A-verified.json',r);put(D/'diagnostic229A-verified.json',r);shutil.copyfile(__file__,E/'verify229A.py');shutil.copytree(E/'diagnostic-source-audit',D/'diagnostic-source-audit',dirs_exist_ok=True)
print(json.dumps({'archive_sha256':r['archive_sha256_raw_bytes'],'selected_cases':21,'all_D2n2_partitions':15,'actual_modes':[0,1],'controls':3,'backend_inactive':True}))
