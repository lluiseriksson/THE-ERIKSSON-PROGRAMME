from pathlib import Path
from collections import defaultdict,Counter
from urllib.request import urlopen,Request
from urllib.parse import urlsplit
import hashlib,unicodedata,json,zipfile,io
import pandas as pd
rev='e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb'
url='https://huggingface.co/datasets/sarahcen/ai-supply-chain/resolve/'+rev+'/data/gsearch_relationship_results.parquet'
digest='89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a'
with urlopen(Request(url,headers={'User-Agent':'Programme-economic-research/1'}),timeout=45) as f:data=f.read(35815746)
if len(data)!=35815745 or hashlib.sha256(data).hexdigest()!=digest: raise ValueError('Data identity mismatch')
cols='link document_date actor_1_name actor_2_name relationship_type relationship_status directionality ai_stack_layers'.split()
import itertools
from collections import defaultdict,Counter
def require(ok,msg):
    if not ok:raise ValueError(msg)
def norm(s):return ' '.join(unicodedata.normalize('NFKC',s).casefold().split())
alphabet={'alphabet','alphabet inc','alphabet inc.','google','google llc','google cloud','deepmind','google deepmind'}
df=pd.read_parquet(io.BytesIO(data),columns=cols)
dates=pd.to_datetime(df.document_date,errors='coerce',utc=True,format='mixed')
inside=(dates>='2022-11-01') & (dates<'2026-11-01')
def ismodel(x):
    if isinstance(x,str):
        if x=='MODELS':return True
        try:x=json.loads(x)
        except ValueError:return False
    return x is not None and 'MODELS' in x
eligible=(df.relationship_type=='PROVISION') & (df.relationship_status=='ESTABLISHED') & df.ai_stack_layers.map(ismodel)
needed=set(s.strip() for s in df.loc[eligible & dates.isna(),'link'] if isinstance(s,str))
known=defaultdict(set)
for s,flag in zip(df.loc[dates.notna(),'link'],inside[dates.notna()]):
    if isinstance(s,str) and s.strip() in needed:known[s.strip()].add(bool(flag))
rows=[];counts=Counter()
for i,r in df[eligible].iterrows():
    a,b=r.actor_1_name,r.actor_2_name
    if r.directionality=='ACTOR_2_TO_ACTOR_1':a,b=b,a
    elif r.directionality!='ACTOR_1_TO_ACTOR_2':continue
    if not all(isinstance(s,str) and s.strip() for s in (a,b,r.link)):continue
    doc=r.link.strip();host=(urlsplit(doc).hostname or '').lower().removeprefix('www.')
    if not host:continue
    if pd.isna(dates[i]):
        flags=known[doc]
        require(len(flags)<=1,'Inconsistent window statuses for an undated document')
        status=('forced_in' if True in flags else 'forced_out') if flags else 'optional'
    else:status='dated_in' if inside[i] else 'dated_out'
    counts[status]+=1
    rows.append((norm(a),norm(b),doc,host,status))
orgs=('anthropic','openai','google','google deepmind','google cloud','deepmind','alphabet')
papers={'PMC11621808','PMC11989924','10.3389/fpls.2024.1468676'}
extract=[]
for a,b,doc,h,s in rows:
    if s!='optional' or not any(id_ in doc for id_ in papers):continue
    if a not in orgs:continue
    others={u for aa,bb,u,hh,ss in rows if aa==a and bb==b and u!=doc and ss=='dated_in' and hh!='anthropic.com'}
    extract.append(dict(source=doc,provider=a,recipient=b,other_dated_docs_without_anthropic_host=len(others)))
assert extract
with zipfile.ZipFile('/content/article-rows.zip','x',zipfile.ZIP_DEFLATED) as z:z.writestr('article-rows.json',json.dumps(extract,indent=2))
print('archive_sha256 '+hashlib.sha256(Path('/content/article-rows.zip').read_bytes()).hexdigest())
