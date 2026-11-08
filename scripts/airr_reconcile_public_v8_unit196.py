import hashlib,json,os,sqlite3,stat
from pathlib import Path
if os.name != 'posix': raise RuntimeError('Existing AIRR Linux host only')
p=Path('/srv/airr-private/historical-revisions/catalogue.json').resolve()
raw=p.read_bytes(); data=json.loads(raw)
import urllib.request
b=urllib.request.urlopen('https://airr.science/papers/ARR-2026-7EPM3V3DP796BBRR/versions/v8/ARR-2026-7EPM3V3DP796BBRR-v8.pdf',timeout=30).read()
if hashlib.sha256(b).hexdigest()!='b68cbb3d02fe96edae263a4ad36c1be471302f488e79cdc8de6f2d771250b3ea' or len(b)!=694866:raise RuntimeError('Public v8 bytes mismatch')
pid='ARR-2026-7EPM3V3DP796BBRR'
entry={'record_id':'arr:record:eeb507b1-b6c7-4996-bc62-a4e7c416be00','version_id':'arr:version:ef75b4a4-baa6-4730-a334-e26ef17ab83f','version':'v8','canonical_sha256':'b68cbb3d02fe96edae263a4ad36c1be471302f488e79cdc8de6f2d771250b3ea','authors':['Lluis Eriksson']}
if data.get(pid)==entry:
 print(json.dumps({'status':'already_reconciled','entry':entry}));raise SystemExit(0)
old=data.get(pid,{})
if old.get('canonical_sha256')!='9070f806e9069fd4b1fa54ec24527bc0cfcc03ddfce91b1206ed9358f6ce70c6':raise RuntimeError('Unexpected v7 hash')
if old.get('version')!='v7' or old.get('record_id')!=entry['record_id'] or old.get('authors')!=entry['authors']:
 raise RuntimeError('Unexpected predecessor; do not overwrite')
db=sqlite3.connect('/srv/airr-private/instance/intake.sqlite3',timeout=15)
db.execute('BEGIN IMMEDIATE')
n=db.execute("select count(*) from historical_revision_grants h join agent_grants g on h.grant_id=g.id where g.state='approved' and g.uses=0 and julianday(g.expires_at)>julianday('now')").fetchone()[0]
if n:raise RuntimeError('Live unused historical grants require reconciliation first')
backup=Path('/srv/airr-private/tep-catalogue-before196-v8.json')
with backup.open('xb') as f:f.write(raw)
prior=dict(data);data[pid]=entry
if any(data[k]!=v for k,v in prior.items() if k!=pid):raise RuntimeError('Unrelated entry changed')
new=(json.dumps(data,sort_keys=True,indent=2)+'\n').encode()
tmp=p.with_name(p.name+'.196.tmp'); st=p.stat()
with tmp.open('xb') as f:f.write(new);f.flush();os.fsync(f.fileno())
os.chmod(tmp,stat.S_IMODE(st.st_mode));os.chown(tmp,st.st_uid,st.st_gid)
os.replace(tmp,p);db.commit();db.close()
if p.read_bytes()!=new:raise RuntimeError('Catalogue readback mismatch')
print(json.dumps({'status':'reconciled_verified_public_v8','old_sha256':hashlib.sha256(raw).hexdigest(),'new_sha256':hashlib.sha256(new).hexdigest(),'active_unused_grants':n,'unrelated_entries_preserved':len(prior)-1,'entry':entry}))
