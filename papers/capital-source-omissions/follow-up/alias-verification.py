from pathlib import Path
from collections import Counter, defaultdict
from urllib.parse import urlsplit
import hashlib,json,re,unicodedata,urllib.request,zipfile
import pyarrow.parquet as pq

pin='e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb'
url='https://huggingface.co/datasets/sarahcen/ai-supply-chain/resolve/'+pin+'/data/gsearch_relationship_results.parquet'
path=Path('/content/data.parquet')
with urllib.request.urlopen(url,timeout=90) as src,path.open('xb') as out:
    while block:=src.read(1048576):out.write(block)
source_sha=hashlib.sha256(path.read_bytes()).hexdigest()
columns='document_date ai_stack_layers relationship_type relationship_status evidence_strength actor_1_type actor_2_type directionality actor_1_name actor_2_name link'.split()
modes={key:defaultdict(set) for key in ('trim','fold')}
stats=Counter()
for batch in pq.ParquetFile(path).iter_batches(columns=columns,batch_size=2048):
    for r in batch.to_pylist():
        stats['input']+=1
        date=str(r['document_date'])[:10]
        layers=r['ai_stack_layers']
        if isinstance(layers,str):
            if layers.startswith('['):layers=json.loads(layers)
            else:layers=[layers]
        if not ('2022-11-01'<=date<='2026-10-31' and 'CAPITAL' in (layers or []) and r['actor_1_type']==r['actor_2_type']=='COMPANY' and r['relationship_status']=='ESTABLISHED' and r['relationship_type']=='INVESTMENT' and r['evidence_strength']=='EXPLICIT' and r['directionality'] in ('ACTOR_1_TO_ACTOR_2','ACTOR_2_TO_ACTOR_1')):continue
        stats['eligible']+=1
        link=urlsplit(r['link'] or '')
        host=(link.hostname or '').lower().removeprefix('www.')
        if not host or link.scheme.lower() not in ('http','https'):continue
        a,b=[(r[key] or '').strip() for key in ('actor_1_name','actor_2_name')]
        if not a or not b:continue
        if r['directionality']=='ACTOR_2_TO_ACTOR_1':a,b=b,a
        for key,graph in modes.items():
            norm=lambda s:' '.join(unicodedata.normalize('NFKC',s).casefold().split()) if key=='fold' else s
            x,y=norm(a),norm(b)
            if x!=y:graph[x,y].add(host)

import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
assert source_sha=='89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a'
g=modes['fold']
aliases={a:'google' for a in ('deepmind','alphabet','gemini')}
graph=defaultdict(set)
counts=Counter()
for (a,b),support in g.items():
    x,y=aliases.get(a,a),aliases.get(b,b)
    if x!=a or y!=b:counts['affected_pairs']+=1
    if x==y:counts['loops_removed']+=1
    else:graph[x,y].update(support)
sources=defaultdict(list)
for (a,b),s in graph.items():sources[a].append(frozenset(s))
leader=sources['nvidia']
hs=sorted(set().union(*leader))
ix={h:i for i,h in enumerate(hs)}
def solve(rival,deg):
    sets=sources[rival] if rival else []
    counts=Counter(leader)
    counts.subtract(s for s in sets if all(h in ix for h in s))
    nh=len(hs);n=nh
    net={};rows=[];rhs=[]
    for s,c in sorted(counts.items(),key=lambda v:sorted(v[0])):
        if not c:continue
        if len(s)==1:
            net[ix[next(iter(s))]]=-c
            continue
        net[n]=-c
        if c>0:
            for h in sorted(s):
                rows.append({n:1,ix[h]:-1});rhs.append(0)
        else:
            rr={ix[h]:1 for h in s};rr[n]=-1
            rows.append(rr);rhs.append(len(s)-1)
        n+=1
    rows.append(net);rhs.append(deg-len(leader))
    A=lil_matrix((len(rows),n))
    for i,row in enumerate(rows):
        for j,v in row.items():A[i,j]=v
    obj=[int(i<nh) for i in range(n)]
    from scipy.optimize import linprog
    lp=linprog(obj,A_ub=A.tocsr(),b_ub=rhs,bounds=(0,1))
    assert lp.success
    scale=1000000
    dual=[(i,round(-v*scale)) for i,v in enumerate(lp.ineqlin.marginals) if -v*scale>=0.5]
    vals=[scale*x for x in obj];bound=0
    for i,p in dual:
        assert p>=0
        bound-=rhs[i]*p
        for j,v in rows[i].items():vals[j]+=p*v
    bound+=sum(min(0,x) for x in vals)
    certified=-(-bound//scale)
    result=milp(np.array(obj,dtype=float),integrality=obj,bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),-np.inf,rhs),options={'time_limit':8.,'mip_rel_gap':0.0})
    witness=None
    if result.x is not None:
        removed={h for h,i in ix.items() if result.x[i]>.5}
        left=sum(bool(s-removed) for s in leader)
        other=sum(bool(s-removed) for s in sets) if rival else deg
        assert left<=other and certified<=len(removed)
        witness={'groups':sorted(removed),'cost':len(removed),'nvidia':left,'rival':other}
    return {'lower':certified,'fraction_numerator':bound,'multipliers':dual,'witness':witness}
ordered=sorted((a for a in sources if a!='nvidia'),key=lambda a:(-len(sources[a]),a))
individuals={a:solve(a,len(sources[a])) for a in ordered if len(sources[a])>40}
tail_max=max(len(sources[a]) for a in ordered if a not in individuals)
tail=solve(None,tail_max)
best,name=min((v['witness']['cost'],a) for a,v in individuals.items() if v['witness'])
S=set(individuals[name]['witness']['groups'])
degrees=Counter(a for (a,b),s in graph.items() if s-S)

out=dict(input_sha256=source_sha,pin=pin,aliases=aliases,counts=counts,pairs=len(graph),investors=len(sources),top=sorted(((len(v),a) for a,v in sources.items()),reverse=True)[:6],lower=min(tail['lower'],*(v['lower'] for v in individuals.values())),upper=best,rival=name,individuals=individuals,tail=tail,leaders_after=sorted(a for a,n in degrees.items() if n==max(degrees.values())),maximum_after=max(degrees.values()))
archive=Path('/content/documented-aliases.zip')
with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('result.json',json.dumps(out,sort_keys=True))
print('archive_sha256 '+hashlib.sha256(archive.read_bytes()).hexdigest())
