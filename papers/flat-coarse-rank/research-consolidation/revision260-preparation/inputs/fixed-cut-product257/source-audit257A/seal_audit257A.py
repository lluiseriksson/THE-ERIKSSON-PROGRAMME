import pathlib, subprocess, hashlib, json, datetime

R=pathlib.Path(r'C:\Trabajo\the-eriksson-programme\perron-spec-210-20261108')
D=pathlib.Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-257\source-audit257A')
SHA='fed201fd10f952a04e638c324dc0e1359711911a'
rel='papers/flat-coarse-rank/research-consolidation/fixed-cut-product257/capacity-class-obstruction257A.txt'
expected='8b92c1aeae67c26832cdd4e53dfcfb62537640d3d2a0a96370e677c3cd1ddbbc'
def git(*args):
    p=subprocess.run(['git','-C',str(R),*args],capture_output=True)
    if p.returncode: raise RuntimeError(p.stderr.decode(errors='replace'))
    return p.stdout
def digest(b): return hashlib.sha256(b).hexdigest()
source=git('show',SHA+':'+rel)
if digest(source)!=expected: raise RuntimeError('Unexpected frozen source digest')
if (R/rel).read_bytes()!=source: raise RuntimeError('Current source differs from frozen Git blob')
if D.exists(): raise RuntimeError('Refuse to replace existing audit')
(D/'subjects').mkdir(parents=True)
subjects=[]
for name,raw,sourcepath,readscope in [
    ('capacity-class-obstruction257A.txt',source,SHA+':'+rel,'Entire proof read and analytically rederived'),
    ('OPERATIONAL-GOVERNANCE-CHARTER.md',git('show',SHA+':docs/OPERATIONAL-GOVERNANCE-CHARTER.md'),SHA+':docs/OPERATIONAL-GOVERNANCE-CHARTER.md','Entire charter read'),
    ('CLAUDE.md',(R/'CLAUDE.md').read_bytes(),str(R/'CLAUDE.md'),'First75 lines directly read; entire raw file retained as context')]:
    (D/'subjects'/name).write_bytes(raw)
    subjects.append({'path':'subjects/'+name,'bytes':len(raw),'sha256_raw':digest(raw),'source':sourcepath,'read_scope':readscope,'normalization':'none'})
prompt='''Mandatory separate source audit under docs/OPERATIONAL-GOVERNANCE-CHARTER.md §4, not another chat. Audit EXACT frozen commit fed201fd10f952a04e638c324dc0e1359711911a at C:\\Trabajo\\the-eriksson-programme\\perron-spec-210-20261108. Read papers/flat-coarse-rank/research-consolidation/fixed-cut-product257/capacity-class-obstruction257A.txt raw SHA256 8b92c1aeae67c26832cdd4e53dfcfb62537640d3d2a0a96370e677c3cd1ddbbc. Adversarially derive/check theorem all steps: arbitrary fixed cyclic transverse partitions, higher actual curl potential, exact corner means, explicit log cutoff square counts and dyadic bounds incl endpoints/seams, MINIMUM-of-cutoffs energy linear q, finite-convolution source commutators, real nonzero witness, constants and restricted nlogn inference. Report any error, failed route, scope overclaim. No math computation/compilation on Windows; analytical reasoning/file/git/hash only. Do not modify proof or repository branch, create no PR, no desktop/browser UI, no Colab needed unless mathematically essential. Capture exact source and directly relied-on subjects in D:\\Datos\\the-eriksson-programme\\autonomia\\evidencia-257\\source-audit257A, raw-byte hashes and full original report/prompt/context. No scores or independence/peer-review claim; actual model identity context exposed Codex/OpenAI GPT6family, exact backend/version/effort unavailable. Preserve full objections/context even if accepted. You may compare256 only explicitly scoped. Audit exact SHA; no branch/body exists externally yet. I will send no inbound messages during audit. Return verdict/full report paths/hashes and subject count. Do not use Python asserts as acceptance checks. No need disposable clone; if created remove safely.'''
(D/'prompt.txt').write_text(prompt+'\n',encoding='utf-8',newline='\n')
(D/'full-report.txt').write_bytes((R/'_tmp'/'audit257A_report.txt').read_bytes())
context={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'task':'/root/fixed_cut257_source_audit','verdict':'ACCEPT_ANALYTICAL_OBSTRUCTION_FOR_FIXED_CUT_PRODUCT_SLICES_ONLY','exact_commit':SHA,'proof_sha256_raw':expected,'git_blob':git('rev-parse',SHA+':'+rel).decode().strip(),'model_identity_exposed':'Codex/OpenAI, GPT-6 family; exact served backend/version/effort not exposed','independence':'Separate child session of same involved programme; inherited parent conversation including construction; not blind or independently established','numerical_grade':None,'formal_check':False,'numerical_experiment':False,'external_literature_audit':False,'inbound_messages_received_during_audit':False,'PR_body_capture':'N/A: no PR/body existed in audit assignment','PR_normalized_body_hash':None,'runtime_created':False,'disposable_clone_created':False,'source_or_branch_mutated':False,'subject_count':len(subjects),'subjects':subjects,'review_context_limit':'Full inherited model conversation is not exported by a tool. This file explicitly records its visibility and limits; prompt.txt is the complete supplied audit assignment, not a fictitious full account transcript.'}
(D/'review-context.json').write_text(json.dumps(context,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
(D/'seal_audit257A.py').write_bytes(pathlib.Path(__file__).read_bytes())
files=[]
for p in sorted(D.rglob('*')):
    if p.is_file():
        b=p.read_bytes(); files.append({'path':p.relative_to(D).as_posix(),'bytes':len(b),'sha256_raw':digest(b)})
manifest={'representation':'Exact raw bytes, no normalization; manifest does not hash itself','subject_count':len(subjects),'subjects':subjects,'files':files}
(D/'hashes.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
for entry in files:
    p=D/entry['path']; raw=p.read_bytes()
    if len(raw)!=entry['bytes'] or digest(raw)!=entry['sha256_raw']: raise RuntimeError('Readback mismatch '+entry['path'])
print(json.dumps({'folder':str(D),'verdict':context['verdict'],'subject_count':len(subjects),'full_report_sha256_raw':digest((D/'full-report.txt').read_bytes()),'hashes_sha256_raw':digest((D/'hashes.json').read_bytes()),'proof_git_blob':context['git_blob']}))
