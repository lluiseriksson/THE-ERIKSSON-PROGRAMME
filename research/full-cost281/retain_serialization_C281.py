"""Metadata-only immutable C source packet; no reviewed source execution."""
from pathlib import Path
import json,hashlib,shutil
P=Path(__file__).resolve().parent
OLD=Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-281\source-preparation-thread-bound-final')
D=OLD.with_name('source-preparation-C')
if D.exists():raise ValueError('Preserve existing C source packet')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(v,f,indent=2);f.write('\n')
D.mkdir(parents=True,exist_ok=False);S=D/'source';S.mkdir();shutil.copytree(OLD/'inputs',D/'inputs')
for p in sorted(P.rglob('*')):
    if p.is_file():
        target=S/p.relative_to(P);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,target)
for name in ['assignment.txt','parent-pre-freeze-correction.txt','parent-thread-correction.txt']:shutil.copyfile(OLD/name,D/name)
assignment="""Pre-execution BLOCKING engineering defect in frozenB, root static inspection: blocks() defines h=tuple((np.array(k)+q)%n), yielding np.int64 entries. audit row uses 'h':list(h), then plain json.dump in dump(blocks.json) has no NumPy encoder -> TypeError. No runtime has been allocated, no relay created. Preserve B and exact current B launch/template/manifest unchanged in version history. Fabricate C minimal mathematical-code delta: h=tuple(int(x) for x in ((np.array(k)+q)%n)); check all other JSON leaves statically for NumPy scalars. No parameter/tolerance/math change. Create diagnostic281C.py, complete B-C diff, rebuild source-bound bootstrap/outer gates/manifest for C and preserve B wrappers beforechanges. Update engineering event/construction context truthfully; B analytical source auditor missed this serialization blocker (reportmustremainimmutable). Do not execute any tests/numerics/runtime, commit or state. Retain C raw source-preparation packet in evidencia281 distinct folder. Return exact hashes and full changes. Parent will obtain separate exact C review before execution.
"""
with (D/'assignment-C.txt').open('x',encoding='utf-8',newline='\n') as f:f.write(assignment)
ctx=json.loads((OLD/'context-and-subjects.json').read_bytes())
ctx.update(preferred_source='source/diagnostic281C.py',preferred_source_sha256=sha(P/'diagnostic281C.py'),runner_manifest_sha256=sha(P/'RUNNER-HASHES.json'),preserved_B_source_sha256=sha(P/'diagnostic281B.py'),preserved_B_history_manifest_sha256=sha(P/'history-281B-before-serialization-C/RUNNER-HASHES.json'),B_C_diff_sha256=sha(P/'B-to-C-full-delta.diff'),construction_C_sha256=sha(P/'CONSTRUCTION281C.md'),supersedes_for_operative_wrapper=str(OLD),prior_packet_manifest_sha256=sha(OLD/'manifest.json'),execution='NONE: source editing/reading/byte hashing/copying/base64 only; no tests, numerical import, WSL, runtime, network, commit or programme-state mutation',engineering_event='Parent static inspection found unsupported NumPy h integer JSON leaves in B; B source/history and previous source audit unchanged. C minimal serialization/source-copy-name repair awaits separate review.',parent_authority_relay_created=False)
dump(D/'context-and-subjects.json',ctx)
rows=[{'path':p.relative_to(D).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(D.rglob('*')) if p.is_file()]
dump(D/'manifest.json',rows)
print(json.dumps({'packet':str(D),'members':len(rows),'manifest_sha256':sha(D/'manifest.json'),'context_sha256':sha(D/'context-and-subjects.json'),'full_construction_C_sha256':sha(P/'CONSTRUCTION281C.md'),'source_C_sha256':sha(P/'diagnostic281C.py'),'runner_manifest_sha256':sha(P/'RUNNER-HASHES.json'),'B_C_diff_sha256':sha(P/'B-to-C-full-delta.diff')},indent=2))
