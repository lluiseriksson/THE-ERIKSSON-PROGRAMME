"""Test one-source failures on all portfolios. Check the three final DOI witnesses directly in the raw exports."""
from pathlib import Path
from urllib.request import urlopen
from urllib.parse import quote,unquote
from collections import Counter
from itertools import combinations
import re,hashlib,json,unicodedata,html
def read(n):return json.loads(Path(n).read_bytes())
def keys(text):
    text=unicodedata.normalize('NFKC',html.unescape(unquote(text))).casefold()
    return ''.join(c for c in text if c.isalnum())
def fault(masks,sources):
    by_budget={}
    for k in range(1,len(sources)+1):
        tests=[]
        for p in combinations(sources,k):
            values=[sum(bool(set(m)&(set(p)-{s})) for m in masks) for s in p]
            tests.append((min(values),p))
        best=max(v for v,p in tests);by_budget[k]=dict(best=best,portfolios=[p for v,p in tests if v==best])
    return by_budget
v=read('replication.json');g=v['groups'];ids=g['initial']['rows'];raw_support={}
for f in read('second-register-files.json')['files']:
    if not f['key'].endswith('.bib') or 'duplicate removal' in f['key']:continue
    s=f['key'][13:-4]; assert s in v['sources'],s
    with urlopen('https://zenodo.org/api/records/16185787/files/'+quote(f['key'],safe='')+'/content',timeout=45) as r:b=r.read(f['size']+1)
    assert len(b)==f['size'] and 'md5:'+hashlib.md5(b).hexdigest()==f['checksum']
    body=keys(b.decode('utf-8-sig'));raw_support[s]={x['id']:{'doi':keys(x['doi']) in body,'title':keys(x['title']) in body} for x in ids}
sources=sorted(v['sources'])
v1=read('first-register.json')['comparisons']['tokens'];v1scores=fault([r['sources'] for r in v1['table']],v1['including_duplicates']['sources'])
scores={k:fault([r['matches'] for r in g[k]['rows']],sources) for k in ['initial','preliminary']}
print(json.dumps(dict(fulltext=raw_support,robustness=dict(first=v1scores,**scores)),indent=2))
