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
fixed=set(['https://pmc.ncbi.nlm.nih.gov/articles/PMC11621808/', 'https://pmc.ncbi.nlm.nih.gov/articles/PMC11989924/', 'https://venturebeat.com/business/braintrust-data-wants-to-make-enterprise-ai-better-with-faster-evaluations', 'https://www.frontiersin.org/journals/plant-science/articles/10.3389/fpls.2024.1468676/full'])
assert {u for a,b,u,h,s in rows if s=='optional' and u in fixed}==fixed
rows=[(a,b,u,h,'forced_in' if s=='optional' and u in fixed else s) for a,b,u,h,s in rows]

def optimum(pos,neg):
    # Maximize the difference of two counts of covered recipient labels.
    pdocs=set().union(*pos.values());ndocs=set().union(*neg.values())
    happy=pdocs-ndocs
    covered0={k for k,v in pos.items() if v & happy}
    todo={k:v for k,v in pos.items() if k not in covered0}
    mixed=sorted(set().union(*todo.values()))
    require(len(mixed)<=22,'Mixed-document budget exceeded: '+str(len(mixed)))
    def delta(chosen):return sum(bool(v&chosen) for v in pos.values())-sum(bool(v&chosen) for v in neg.values())
    best=-1;chosen=happy.copy()
    for mask in range(1<<len(mixed)):
        selected=happy|{m for j,m in enumerate(mixed) if mask&(1<<j)}
        value=delta(selected)
        if value>best:best,chosen=value,selected
    require(best==delta(chosen),'Signed coverage witness mismatch')
    return best,chosen,len(mixed)
def selftest():
    tests=0
    for ix in range(1,64):
        ds=range(4)
        p={j:{u for u in ds if ((ix*(u+1)+j)%(j+3))!=0} for j in range(4)}
        n={j:{u for u in ds if ((ix+j*u)%(j+2))==0} for j in range(3)}
        val,_,_=optimum(p,n)
        brute=max(sum(bool(set(s)&v) for v in p.values())-sum(bool(set(s)&v) for v in n.values()) for k in range(5) for s in itertools.combinations(ds,k))
        require(val==brute,'Small brute-force discrepancy');tests+=1
    return tests
def audit(merge,cut):
    def lab(s):return 'alphabet [selected family]' if merge and s in alphabet else s
    base=defaultdict(set);extra=defaultdict(lambda:defaultdict(set));optional=set()
    for a,b,d,h,status in rows:
        if cut and h=='anthropic.com':continue
        a,b=lab(a),lab(b)
        if a==b:continue
        if status in {'dated_in','forced_in'}:base[a].add(b)
        elif status=='optional':extra[a][b].add(d);optional.add(d)
    providers=set(base)|set(extra)
    for a in providers:
        for b in base[a]:extra[a].pop(b,None)
    upper={a:len(base[a])+len(extra[a]) for a in providers}
    floor=max(len(base[a]) for a in providers)
    contenders=sorted(a for a in providers if upper[a]>=floor)
    def order(chosen):
        edges=defaultdict(set)
        for a,b,d,h,status in rows:
            if cut and h=='anthropic.com':continue
            a,b=lab(a),lab(b)
            if a!=b and (status in {'dated_in','forced_in'} or (status=='optional' and d in chosen)):edges[a].add(b)
        return sorted(((a,len(z)) for a,z in edges.items()),key=lambda x:(-x[1],x[0]))
    panels=[];known_winners={}
    def check_world(s):
        ranked=order(s);top=ranked[0][1];winners=tuple(n for n,d in ranked if d==top)
        ids=sorted(hashlib.sha256(u.encode()).hexdigest() for u in s)
        known_winners.setdefault('|'.join(winners),dict(top=ranked[:4],included_optional_url_sha256=ids))
        return dict(ranked),ids
    check_world(set());check_world(optional)
    for a,b in itertools.combinations(contenders,2):
        gap=len(base[a])-len(base[b]);lo,l,low_k=optimum(extra[b],extra[a]);hi,h,high_k=optimum(extra[a],extra[b])
        left,lu=check_world(l);right,hu=check_world(h)
        require(left[a]-left[b]==gap-lo and right[a]-right[b]==gap+hi,'Raw row witness fails')
        panels.append(dict(a=a,b=b,minimum=gap-lo,maximum=gap+hi,ambiguous=[low_k,high_k],minimum_urls=lu,maximum_urls=hu))
    return dict(optional_docs=len(optional),contenders={a:[len(base[a]),upper[a]] for a in contenders},excluded_rivals_maximum=max((n for a,n in upper.items() if a not in contenders),default=0),baseline=order(set())[:4],all_in=order(optional)[:4],pairwise=panels,achieved_winners=known_winners)
results={'file_sha256':digest,'revision':rev,'undated_layer_rows':int((eligible & dates.isna()).sum()),'eligible_statuses':dict(counts),'tests':selftest(),'scenarios':{}}
for g in (False,True):
    for c in (False,True):results['scenarios'][str(int(g))+str(int(c))]=audit(g,c)
out=Path('/content/date-conditioned.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('date-conditioned.json',json.dumps(results,indent=2))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
