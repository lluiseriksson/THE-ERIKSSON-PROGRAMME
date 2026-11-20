"""External fixed-budget audit of vowel insertion. See external-protocol.md."""
import contextlib
import hashlib
import io
import json
import re
import runpy
from collections import Counter
from fractions import Fraction
from urllib.request import urlopen
import pyarrow.parquet as pq

with contextlib.redirect_stdout(io.StringIO()):
    padt = runpy.run_path('padt-transfer.py')
pin = 'aa311213e44e4cab6cc3f2848daacd753adc1ce1'
url = 'https://huggingface.co/datasets/Misraj/SadeedDiac-25/resolve/'+pin+'/data/train-00000-of-00001.parquet'
with urlopen(url, timeout=40) as response:
    data = response.read()
digest = hashlib.sha256(data).hexdigest()
assert digest == 'd727d08f1e18ac514526ad572c26d9647bdc08395ef9aceb8673c0f69fdd08a9'
records = pq.read_table(io.BytesIO(data), columns=['input','output']).to_pylist()
assert len(records)==1200
tokens = re.compile('[ء-يً-ْٰ]+')
diacs = re.compile('[ً-ْٰـ]')
def words(s):
    return [w for t in tokens.findall(s) if (w:=t.replace('ـ','')) and diacs.sub('',w)]
def bare(w):
    return diacs.sub('',w)
def eligible(b):
    return b.startswith('ال') and len(b)>=5 and b not in padt['excluded'] and b!='العقود' and not re.search('(?:ان|ون|ين|ات|[يىاءئؤو])$',b)
def windows(s):
    return (s[i:i+64] for i in range(len(s)-63))
texts=[''.join(map(bare,words(r['input']))) for r in records]
cand={v for s in texts for v in windows(s)}
hits=set()
for split in ['train','dev','test']:
    letters=[]
    for line in padt[split].decode().splitlines()+['']:
        t=line.split('\t')
        if len(t)<10:
            if letters:
                hits.update(x for x in windows(''.join(letters)) if x in cand)
                letters=[]
        elif t[0].isdigit():
            letters.extend(map(bare,words(t[1])))
seen=set()
flow=Counter(); docs=[]
for ix,(r,s) in enumerate(zip(records,texts)):
    flow['input']+=1
    if s in seen:
        flow['duplicate']+=1
        continue
    seen.add(s)
    if any(x in hits for x in windows(s)):
        flow['padt_overlap']+=1
        continue
    inc=words(r['input']);out=words(r['output'])
    if list(map(bare,inc))!=list(map(bare,out)):
        flow['unaligned']+=1
        continue
    flow['used']+=1
    cell=Counter()
    for prev,current in zip(out,out[1:]):
        b=bare(current)
        if not eligible(b):continue
        flow['bare_eligible']+=1
        suffix=re.search('[ً-ْٰ]*$',current)[0]
        short=[v for v in suffix if v in 'َُِ']
        if len(short)!=1 or re.search('[ًٌٍْ]',suffix):continue
        flow['scored']+=1
        key=bare(prev)
        cu=padt['cue'](key)
        band,pred=(100,cu[1]) if cu else padt['table'](key)
        if band<60:continue
        group='base' if band>=80 else str(band)
        cell[group]+=1
        cell[group+'_err']+=int(pred!=short[0])
    docs.append(cell)
def gain(c):
    if not c['77'] or c['60']<c['77']:return None
    return Fraction(c['77_err'])-Fraction(c['77']*c['60_err'],c['60'])
def summary(docs):
    c=sum(docs,Counter())
    v=gain(c)
    loo=[gain(c-d) for d in docs]
    loo=[x for x in loo if x is not None]
    return dict(cells=dict(c),gain=str(v) if v is not None else None,original_fills=c['base']+c['77'],original_errors=c['base_err']+c['77_err'],alternative_errors=str(c['base_err']+c['77_err']-v) if v is not None else None,informative_paragraphs={k:sum(d[k]>0 for d in docs) for k in ['77','60']},leave_one_out_range=[str(min(loo)),str(max(loo))] if loo else None)
assert sum(flow[k] for k in ['duplicate','padt_overlap','unaligned','used'])==len(records)
print(json.dumps(dict(pin=pin,sha256=digest,padt_pin=padt['rev'],flow=dict(flow),analysis=summary(docs)),indent=2))
