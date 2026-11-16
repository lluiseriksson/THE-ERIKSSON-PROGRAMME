"""Prospective verified base64 chunks -> exact returnZIP; no download-event claims."""
import json,base64,hashlib
from pathlib import Path
from atomic354A import publish_bytes,require
from validate354A import safe_names,SOURCE,digest
BASE=Path(__file__).resolve().parent
plan=json.loads((BASE/'ACTUAL-CHUNKS.json').read_bytes())
require(plan['source']==SOURCE and plan['input_name']=='tep354D-return.zip','Actual source/input')
require(type(plan['bytes']) is int and 0<plan['bytes']<512_000_000,'Transport bound')
parts=plan['parts'];require(isinstance(parts,list) and parts and len(parts)<10000,'Actual bounded parts')
safe_names([r['path'] for r in parts]);pieces=[]
for index,row in enumerate(parts):
    require(type(row['index']) is int and row['index']==index,'Sequential actual chunks')
    path=BASE/row['path'];require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(BASE),'Actual regular chunk')
    encoded=path.read_bytes();require(len(encoded)<4_000_000,'Bounded encoded chunk')
    raw=base64.b64decode(encoded,validate=True)
    require(type(row['bytes']) is int and row['bytes']>0 and len(raw)==row['bytes'] and digest(raw)==row['sha256'],'Actual chunk hash/length')
    pieces.append(raw)
    require(sum(len(x) for x in pieces)<=plan['bytes'],'Actual aggregate length bound')
raw=b''.join(pieces)
publish_bytes(BASE/'tep354D-return.zip',raw,plan['bytes'],plan['sha256'])
receipt=dict(source=SOURCE,bytes=len(raw),sha256=digest(raw),parts=len(parts),
             method='strict-base64-hash-before-atomic-no-clobber-publication-and-readback',download_event_claim=False)
with (BASE/'transport-readback.json').open('x',encoding='utf-8') as f:json.dump(receipt,f,indent=2);f.write('\n')
print(json.dumps(receipt))
