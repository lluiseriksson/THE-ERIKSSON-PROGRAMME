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
cols='actor_1_type actor_2_type link document_date actor_1_name actor_2_name relationship_type relationship_status directionality ai_stack_layers'.split()
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

fixed=set(['009af8f7d8a12d2d31aa79ba3d11682fc6effe3a930c5972b839300910331437', '099dec7e6e54a2f060bc940a4c381c869b4bfc36912ea7ad7427928c6acea044', '0c99e963f5bd835d9a6d74b3895ab386cfd57f65b6e4f131bd0ed84f6b3d34b7', '27bd63290523d3dfbc78052cf535cb1b0165dd5eed04e1a0144daca05a619d82', '49aaecedf81bf410138165d2bfdf9fcf8d156c1f261fce496c6b3b5b0695a64c', '4f60934e72557da25f0ba23cd733c283ee0c7ba83ac9468cd3324e778b829e16', '57b09e4eef515960a088dd3398f78be71b9de51256b1d1e1b3ad45294620983f', '6542423729abb404ef420173970f7ccfe8b75ee260be54a046adbc13d8d39fbc', '6ba413a3c70849168a40cc1aeefbbd42ebc0112aa887a83ed0a7689ee35b92f5', '8593db728cb2741e8e41d28fb3b3e3ea4a31d6167cb21a8a6bc96c5cde501a05', '88b85cf301fd7d18879252c36d4b293b971c0c30d6cd74ab37484553873631e0', '994677f942a8a1042c66a9c287e47a67aaa41f8e3cbeb67cd1e1eb1af05192f9', 'bc682b9a867a95ef6f59fc51c7061eb30ea86a24b275453ade00a60676a58f73', 'ce43a07820ea43d7f108c9fe821e0a1c0956703a67e752c73749d1a6d1da9112', 'd5f8809630a84cca023bcf0bcf0f63a0de2c0e9a73ec9f4981e58e100f8199ec', 'de6fb2bcd731a49fa77d913efab32119557ca215889c8e54408601f2cadb8b8f', 'ed78974fb39c971768135ca59bc55bacbf39f105782d6a19e056a26c86bc4dcb', 'fbd9377008da358e699bd1389dd71b433e029cabf222521d776fadf8ab417545'])
rows=[]
def keyid(doc):return hashlib.sha256(doc.encode()).hexdigest()
results={};audited=set()
for idx,r in df[eligible].iterrows():
    a,b,ta,tb=r.actor_1_name,r.actor_2_name,r.actor_1_type,r.actor_2_type
    if r.directionality=='ACTOR_2_TO_ACTOR_1':a,b,ta,tb=b,a,tb,ta
    elif r.directionality!='ACTOR_1_TO_ACTOR_2':continue
    if not all(isinstance(s,str) and s.strip() for s in (a,b,r.link)):continue
    u=r.link.strip();h=(urlsplit(u).hostname or '').lower().removeprefix('www.')
    if not h:continue
    k=keyid(u)
    if pd.isna(dates[idx]):
        flags=known[u]
        assert len(flags)<=1
        if True in flags or k in fixed:s='inside'
        elif False in flags:continue
        else:s='optional'
    elif inside[idx]:s='inside'
    else:continue
    a,b=norm(a),norm(b)
    if a=='openai' and any(q in u for q in ('PMC11621808','PMC11989924','10.3389/fpls.2024.1468676')):audited.add((k,b,str(ta),str(tb)))
    rows.append((a,b,k,h,s,str(ta),str(tb)))
def run(which,group,cut):
    base=defaultdict(set);docs=defaultdict(set)
    def groupname(s):return 'alphabet [selected family]' if group and s in alphabet else s
    for a,b,k,h,s,ta,tb in rows:
        if which!='all' and tb!='COMPANY' or which=='both' and ta!='COMPANY':continue
        if cut and h=='anthropic.com':continue
        a,b=groupname(a),groupname(b)
        if a==b:continue
        if s=='inside':base[a].add(b)
        else:docs[k].add((a,b))
    high=defaultdict(set,{a:x.copy() for a,x in base.items()})
    for pairs in docs.values():
        for a,b in pairs:high[a].add(b)
    ordered=sorted(base,key=lambda a:-len(base[a]));second=len(base[ordered[1]])
    pool={a for a in high if len(high[a])>=second}
    changed={k:{(a,b) for a,b in es if a in pool and b not in base[a]} for k,es in docs.items()}
    keys=sorted(k for k,es in changed.items() if es)
    out=dict(rivals=sorted(pool),decisions=len(keys),dated_top=sorted([(n,len(x)) for n,x in base.items()],key=lambda p:(-p[1],p[0]))[:5],bounds={a:[len(base[a]),len(high[a])] for a in pool})
    if len(keys)>16:return out
    wins=defaultdict(set);ex=defaultdict(dict)
    for mask in range(1<<len(keys)):
        chosen=[k for j,k in enumerate(keys) if mask & (1<<j)]
        xs={a:base[a].copy() for a in pool}
        for k in chosen:
            for a,b in changed[k]:xs[a].add(b)
        ranked=sorted(((-len(v),a) for a,v in xs.items()))
        lead=-ranked[0][0];winners='|'.join(sorted(a for a,v in xs.items() if len(v)==lead));m=ranked[1][0]-ranked[0][0]
        wins[winners].add(m)
        if str(m) not in ex[winners]:ex[winners][str(m)]=chosen
    return dict(out,winning_margins={a:sorted(v) for a,v in wins.items()},witnesses=ex,worlds=2**len(keys))
for which in ('all','recipients','both'):
    results[which]={}
    for g in (0,1):
        for cut in (0,1):results[which][str(g)+str(cut)]=run(which,g,cut)
for k,(winner,lo,hi) in {'00':('anthropic',22,26),'01':('anthropic',6,10),'10':('anthropic',6,10),'11':('alphabet [selected family]',6,10)}.items():
    assert results['all'][k]['winning_margins']=={winner:list(range(lo,hi+1))}
out=Path('/content/recipient-types.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('recipient-types.json',json.dumps(dict(cells=results,source_type_examples=sorted(audited)),indent=2))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
