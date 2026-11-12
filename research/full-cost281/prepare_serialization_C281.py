"""Metadata-only C serialization repair. Never imports or executes diagnostic."""
from pathlib import Path
import json,hashlib,shutil,difflib,base64
P=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,data):
    with p.open('xb') as f:f.write(data)
old_manifest='1b9d3d115b68f1250803c561a25728bc717d7b86218f2f2d071c7bdb5d97f1c7'
if sha(P/'RUNNER-HASHES.json')!=old_manifest:raise ValueError('Exact frozen B runner manifest differs')
if sha(P/'diagnostic281B.py')!='495a00952c4869f313c2245c1a089498fe8775dccb789ee617a078271eb23ee0':raise ValueError('Frozen B source differs')
HIST=P/'history-281B-before-serialization-C'
HIST.mkdir(exist_ok=False)
names=['diagnostic281B.py','launch281.py','bootstrap281-template.txt','run_owned_after_gate.ps1','capture_cli_atomic.ps1','readback_after_stop.ps1','RUNNER-HASHES.json','CONSTRUCTION281.md']
for name in names:shutil.copyfile(P/name,HIST/name)
old=(P/'diagnostic281B.py').read_bytes();a=b'h=tuple((np.array(k)+q)%n)';b=b'h=tuple(int(x) for x in ((np.array(k)+q)%n))'
if old.count(a)!=1:raise ValueError('Exact single h serialization repair target absent')
raw=old.replace(a,b).replace(b"shutil_source=E/'diagnostic281B.py'",b"shutil_source=E/'diagnostic281C.py'")
write(P/'diagnostic281C.py',raw);H=sha(P/'diagnostic281C.py')
diff=''.join(difflib.unified_diff(old.decode('utf-8').splitlines(True),raw.decode('utf-8').splitlines(True),fromfile='immutable-B/diagnostic281B.py',tofile='preferred-C/diagnostic281C.py'))
write(P/'B-to-C-full-delta.diff',diff.encode('utf-8'))
template=(P/'bootstrap281-template.txt').read_text(encoding='utf-8').replace("path=E/'diagnostic281B.py'","path=E/'diagnostic281C.py'")
with (P/'bootstrap281-template.txt').open('w',encoding='utf-8',newline='\n') as f:f.write(template)
with (P/'launch281.py').open('w',encoding='utf-8',newline='\n') as f:f.write(template.replace('EMBEDDED_HASH',H).replace('EMBEDDED_BASE64',base64.b64encode(raw).decode()))
outer=(P/'run_owned_after_gate.ps1').read_text(encoding='utf-8').replace('495a00952c4869f313c2245c1a089498fe8775dccb789ee617a078271eb23ee0',H)
with (P/'run_owned_after_gate.ps1').open('w',encoding='utf-8',newline='\n') as f:f.write(outer)
rows=json.loads((P/'RUNNER-HASHES.json').read_bytes())
for row in rows:
    if row['path']=='diagnostic281B.py':row['path']='diagnostic281C.py'
    row['bytes']=(P/row['path']).stat().st_size;row['sha256']=sha(P/row['path'])
with (P/'RUNNER-HASHES.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(rows,f,indent=2);f.write('\n')
print(json.dumps({'source_C_sha256':H,'source_C_bytes':len(raw),'runner_manifest_sha256':sha(P/'RUNNER-HASHES.json'),'launch_sha256':sha(P/'launch281.py'),'B_C_diff_sha256':sha(P/'B-to-C-full-delta.diff'),'B_history_manifest_sha256':sha(HIST/'RUNNER-HASHES.json')},indent=2))
