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
def minimum_assignments(group,cut):
    def label(s):return 'alphabet [selected family]' if group and s in alphabet else s
    baseline=defaultdict(set);docs=defaultdict(set)
    for a,b,url,host,s in rows:
        if cut and host=='anthropic.com':continue
        a,b=label(a),label(b)
        if a==b:continue
        if s in ('dated_in','forced_in'):baseline[a].add(b)
        elif s=='optional':docs[url].add((a,b))
    top=max(baseline,key=lambda a:len(baseline[a]));base=len(baseline[top])
    possible=defaultdict(set)
    for p in docs.values():
        for a,b in p:possible[a].add(b)
    res=[]
    for rival in sorted(possible):
        if rival==top or len(possible[rival]|baseline[rival])<base:continue
        add={a:{b:j for j,b in enumerate(sorted(possible[a]-baseline[a]))} for a in (rival,top)}
        states={(0,0):()};nd=0
        for u,pairs in sorted(docs.items()):
            masks={a:sum(1<<j for b,j in add[a].items() if (a,b) in pairs) for a in add}
            if not masks[rival]:continue
            nd+=1;new={}
            for (pos,neg),w in states.items():
                key=(pos|masks[rival],neg|masks[top]);q=w+(u,)
                old=states.get(key);other=new.get(key)
                if (old is None or len(q)<len(old)) and (other is None or len(q)<len(other)):new[key]=q
            states.update(new);require(len(states)<=1500000,'Coverage mask limit')
        initial=len(baseline[rival])-base
        margins={k:initial+k[0].bit_count()-k[1].bit_count() for k in states}
        def shortest(threshold):
            candidates=[(len(w),w,margin) for k,w in states.items() if (margin:=margins[k])>=threshold]
            if not candidates:return None
            cost,w,margin=min(candidates);selected=set(w);sets={top:set(),rival:set()}
            for a,b,u,h,s in rows:
                if cut and h=='anthropic.com':continue
                a,b=label(a),label(b)
                if a in sets and a!=b and (s in ('dated_in','forced_in') or (s=='optional' and u in selected)):sets[a].add(b)
            require(len(sets[rival])-len(sets[top])==margin,'Raw witness mismatch')
            return dict(docs=cost,margin=margin,counts={a:len(b) for a,b in sets.items()},included=[hashlib.sha256(u.encode()).hexdigest() for u in w])
        res.append(dict(rival=rival,baseline_margin=initial,maximum=max(margins.values()),tie_or_better=shortest(0),strict_win=shortest(1),relevant_urls=nd,states=len(states)))
    return dict(dated_leader=top,rivals=res)
expected={'00':[],'01':[2],'10':[4],'11':[0]}
results={}
for g in (False,True):
    for c in (False,True):
        key=str(int(g))+str(int(c));v=minimum_assignments(g,c)
        require([r['maximum'] for r in v['rivals']]==expected[key],'DP differs from independent signed coverage result')
        results[key]=v
out=Path('/content/date-witness.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('date-witness.json',json.dumps(results,indent=2))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
