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
table=pd.read_parquet(io.BytesIO(data),columns=cols)
table=table[(table.relationship_type=='PROVISION') & (table.relationship_status=='ESTABLISHED')]
def layer(x):
 if isinstance(x,str):
  if x=='MODELS':return True
  try:x=json.loads(x)
  except ValueError:return False
 return x is not None and 'MODELS' in x
table=table[table.ai_stack_layers.map(layer)]
dt=pd.to_datetime(table.document_date,errors='coerce',utc=True,format='mixed')
undated=int(dt.isna().sum())
table=table[(dt>='2022-11-01') & (dt<'2026-11-01')]
total=len(table)
rows=[]
for r in table.itertuples():
 a,b=r.actor_1_name,r.actor_2_name
 if r.directionality=='ACTOR_2_TO_ACTOR_1':a,b=b,a
 elif r.directionality!='ACTOR_1_TO_ACTOR_2':continue
 if not all(isinstance(s,str) and s.strip() for s in (a,b,r.link)):continue
 host=(urlsplit(r.link).hostname or '').lower().removeprefix('www.')
 if host:rows.append((a,b,host))
if not rows or total<len(rows): raise ValueError('Selection mismatch')
def norm(s):return ' '.join(unicodedata.normalize('NFKC',s).casefold().split())
from itertools import combinations
import numpy as np
def check(ok,message):
    if not ok:raise ValueError(message)
google_names={'google','google llc','google cloud','google deepmind','deepmind','alphabet','alphabet inc.','alphabet inc'}
surfaces={'anthropic':('anthropic.com','claude.com','claude.ai'),'openai':('openai.com',),'google':('google.com','blog.google','deepmind.google','deepmind.com')}
def dns(h,domain):return h==domain or h.endswith('.'+domain)
def analyze_family(give,take):
    def label(s,group):
        k=norm(s)
        return 'alphabet [selected family]' if group and k in google_names else k
    edges=defaultdict(set)
    for a,b,h in rows:
        if norm(a)==norm(b):continue
        aa,bb=label(a,give),label(b,take)
        if aa!=bb:edges[aa,bb].add(h)
    hosts=sorted({h for a,b,h in rows if norm(a)!=norm(b)});providers=sorted({a for a,b in edges})
    H={h:i for i,h in enumerate(hosts)};N={a:i for i,a in enumerate(providers)}
    base=np.zeros(len(N),dtype=int);single=np.zeros((len(H),len(N)),dtype=int);double=defaultdict(list)
    for (a,b),support in edges.items():
        j=N[a];base[j]+=1
        if len(support)==1:single[H[next(iter(support))],j]+=1
        elif len(support)==2:
            i,k=sorted(H[h] for h in support);double[i].append((k,j))
    name='anthropic';lead=N[name]
    check(name in providers,'Reference label absent')
    def direct(removed):
        z=Counter(a for (a,b),support in edges.items() if support-removed)
        best=sorted(z,key=lambda n:(-z[n],n));other=next(n for n in best if n!=name)
        return dict(top=[[n,z[n]] for n in best[:4]],margin=z[name]-z[other],initial_leader_count=z[name])
    out=[];single_bad=[]
    for i,host in enumerate(hosts):
        x=base-single[i];left=int(x[lead]);x[lead]=-1;margin=left-int(x.max())
        if margin<=0:
            check(direct({host})['margin']==margin,'single check mismatch')
            single_bad.append([host,margin])
    for i in range(len(hosts)-1):
        x=base-single[i]-single[i+1:]
        for k,j in double[i]:x[k-i-1,j]-=1
        initial=x[:,lead].copy();x[:,lead]=-1;g=initial-x.max(axis=1)
        for row in np.flatnonzero(g<=0):
            k=i+int(row)+1;v=direct({hosts[i],hosts[k]});check(v['margin']==g[row],'pair differs');out.append([hosts[i],hosts[k],v['margin']])
    outcomes={}
    groups={s:{h for h in hosts if any(dns(h,k) for k in suffixes)} for s,suffixes in surfaces.items()}
    for k in range(4):
        for subset in combinations(groups,k):
            removed=set().union(*(groups[s] for s in subset))
            v=direct(removed)
            # Rebuild from raw source rows rather than the stored pair-support sets.
            remap=defaultdict(set)
            for a,b,h in rows:
                if h not in removed and norm(a)!=norm(b) and label(a,give)!=label(b,take):remap[label(a,give)].add(label(b,take))
            check(v['top']==[[n,len(remap[n])] for n in sorted(remap,key=lambda n:(-len(remap[n]),n))[:4]],'raw rows mismatch')
            outcomes['+'.join(subset) or 'none']=dict(**v,removed_hosts=sorted(removed))
    return dict(universe=len(edges),providers=len(N),hosts=len(H),initial_leader=name,observed_aliases=sorted(google_names & {norm(s) for a,b,h in rows for s in (a,b)}),cuts=outcomes,adverse_singles=single_bad,losing_pairs=sum(v<0 for _,_,v in out),tied_pairs=sum(v==0 for _,_,v in out),worst_pair=min((v for _,_,v in out),default=None))
result={str(int(g))+str(int(t)):analyze_family(g,t) for g in (False,True) for t in (False,True)}
check(all(r['hosts']==541 for r in result.values()),'host universe drift')
check(result['00']['losing_pairs']==2 and result['00']['tied_pairs']==0 and not result['00']['adverse_singles'],'baseline')
last=result['11']
check(last['losing_pairs']==1626+8*sum(v<0 for _,v in last['adverse_singles']),'padded loss count')
check(last['tied_pairs']==569+8*sum(v==0 for _,v in last['adverse_singles']),'padded tie count')
out=Path('/content/factorial.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('factorial.json',json.dumps(result,indent=2))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
