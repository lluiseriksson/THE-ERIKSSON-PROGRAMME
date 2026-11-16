"""Prospective354D launch only. Never run locally; separate static review required."""
import os, sys, json, hashlib, subprocess, re, zipfile
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
P = Path(__file__).resolve().parent
SOURCE = '8e452190b8f7d3f7382ba2e6c05d0f14fa9c3dc5'
MARKER_SHA = '968d66a7b491c7728f2ab009dcb54ac0025d6f474de6f3734f66b8809f6c18a8'
def need(ok, msg):
    if not ok: raise ValueError(msg)
def sha(b): return hashlib.sha256(b).hexdigest()
def now(): return datetime.now(timezone.utc).isoformat()
def put(path, value):
    with path.open('xb') as f: f.write((json.dumps(value, indent=2)+'\n').encode())
def closed_exit(path, value):
    need(type(value) is int and not path.exists(), 'New native exit required')
    temp = path.with_suffix(path.suffix+'.tmp')
    with temp.open('xb') as f:
        f.write((str(value)+'\n').encode('ascii')); f.flush(); os.fsync(f.fileno())
    raw = temp.read_bytes()
    need(re.fullmatch(rb'-?[0-9]+\n', raw) is not None and int(raw)==value, 'Native decimal exit')
    os.replace(temp,path); need(path.read_bytes()==raw,'Exit readback')
def child(name, argv):
    start = now()
    with (P/(name+'.stdout')).open('xb') as out, (P/(name+'.stderr')).open('xb') as err:
        proc = subprocess.Popen(argv,cwd=P,stdout=out,stderr=err)
        code = proc.wait()
        out.flush(); os.fsync(out.fileno()); err.flush(); os.fsync(err.fileno())
    closed_exit(P/(name+'.exit'),code)
    return dict(argv=argv,actual_exit=code,started_at=start,finished_at=now())
need(os.name=='posix' and Path('/content').is_dir(), 'Own Colab Linux only')
need(not (P/'launch-receipt354D.json').exists(), 'Fresh launch; never overwrite prior evidence')
need(not Path('/content/tep354D-build-01').exists() and not Path('/content/tep354D-build-01-results.zip').exists(), 'Fresh build paths')
need(not Path('/content/tep354D-return.zip').exists(), 'Fresh return path')
for path in P.rglob('*'):
    need(not path.is_symlink(), 'Packet symlink not allowed')
manifest = json.loads((P/'PREPARATION-MANIFEST.json').read_bytes())
seen = set()
for row in manifest['payloads']:
    name=row['path']
    need(isinstance(name,str) and name and '\\' not in name and not PurePosixPath(name).is_absolute()
         and all(x not in ('','.','..') for x in name.split('/')) and name not in seen, 'Manifest path')
    seen.add(name); path=P/name
    need(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(P), 'Manifest input absent/unsafe')
    raw=path.read_bytes()
    need(len(raw)==row['bytes'] and sha(raw)==row['sha256'], 'Preparation payload changed: '+name)
gate = json.loads((P/'gates'/'authorization.json').read_bytes())
need(gate['source']==SOURCE and gate['status']=='READY_AFTER_ACTUAL_PARENT_REVIEW', 'Actual parent gate needed')
need(gate['reviewed_builder_sha256']==sha((P/'build354D.py').read_bytes()), 'Builder not reviewed version')
need(gate['reviewed_launcher_sha256']==sha(Path(__file__).read_bytes()), 'Launcher not reviewed version')
for key in ('source_integration_review','production_engineering_review','required_ci'):
    row=gate[key]; name=row['path']
    need(isinstance(name,str) and name and '\\' not in name and not PurePosixPath(name).is_absolute()
         and all(x not in ('','.','..') for x in name.split('/')), 'Unsafe gate receipt path')
    path=P/'gates'/name
    need(row['source']==SOURCE and row['status']=='ACCEPTED' and path.is_file()
         and path.resolve().is_relative_to((P/'gates').resolve()) and sha(path.read_bytes())==row['sha256'], 'Gate receipt mismatch')
owner=gate['owner_observation']
need(owner['own_runtime'] is True and owner['runtime_kind']=='CPU' and bool(owner['session_reference'])
     and bool(owner['observed_at']), 'Actual own-session observation required')
need(sha((P/'mark_artifact_operation_started.mjs').read_bytes())==MARKER_SHA, 'Official marker bytes changed')
# Last command before the first authoring command. No marker is executed in preparation.
marker=child('marker354D',['node',str(P/'mark_artifact_operation_started.mjs'),
                        '--operation-kind','create','--expected-output-count','1','--output-format','pdf'])
need(marker['actual_exit']==0,'Marker failed; do not run builder')
put(P/'launch-receipt354D.json',dict(source=SOURCE,builder_sha256=gate['reviewed_builder_sha256'],
    launcher_sha256=gate['reviewed_launcher_sha256'],gate_sha256=sha((P/'gates'/'authorization.json').read_bytes()),
    owner_observation=owner,marker_actual_exit=marker['actual_exit'],marker=marker,created_at=now()))
result=child('builder354D',[sys.executable,str(P/'build354D.py')])
put(P/'launch-result354D.json',dict(source=SOURCE,builder=result,finished_at=now(),
    owned_runtime_closed=False,closure_evidence='MUST_BE_OBSERVED_AFTER_BYTE_RETURN',
    billing_units=None,exact_pdf_review=None))
archive=Path('/content/tep354D-build-01-results.zip')
files=[P/n for n in ('launch-receipt354D.json','launch-result354D.json','marker354D.stdout',
       'marker354D.stderr','marker354D.exit','builder354D.stdout','builder354D.stderr','builder354D.exit')]
if archive.is_file(): files.append(archive)
manifest=[dict(path=f.name,bytes=f.stat().st_size,sha256=sha(f.read_bytes())) for f in files]
outer=Path('/content/tep354D-return.zip')
with zipfile.ZipFile(outer,'x',zipfile.ZIP_DEFLATED) as z:
    for f in files: z.write(f,f.name)
    z.writestr('RETURN-MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(source=SOURCE,return_path=str(outer),bytes=outer.stat().st_size,
                     sha256=sha(outer.read_bytes()),builder_actual_exit=result['actual_exit'])))
if result['actual_exit']!=0: raise RuntimeError('Failed354D: preserve complete returned evidence')
