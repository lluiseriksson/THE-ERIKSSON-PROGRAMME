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
assert source_sha=='89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a'
import numpy as np
import scipy
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

partners=defaultdict(list)
for (investor,partner),s in modes['fold'].items():
    partners[investor].append(tuple(sorted(s)))
lead=partners['nvidia']
degree=len(lead)
hosts=sorted({h for s in lead for h in s})
index={h:i for i,h in enumerate(hosts)}
assert degree==154
D=1000000
budget=37
def case(rival,baseline):
    supports=partners[rival] if rival else []
    counts=Counter(lead)
    counts.subtract(s for s in supports if all(h in index for h in s))
    net={}
    rows=[]
    rhs=[]
    nh=len(hosts)
    nvar=nh
    for s,c in sorted(counts.items()):
        if not c:continue
        if len(s)==1:
            net[index[s[0]]]=-c
            continue
        j=nvar
        nvar+=1
        net[j]=-c
        if c>0:
            for h in s:
                rows.append({j:1,index[h]:-1})
                rhs.append(0)
        else:
            row={index[h]:1 for h in s}
            row[j]=-1
            rows.append(row)
            rhs.append(len(s)-1)
    slack=nvar
    net[slack]=-1
    nvar+=1
    rows.append(net)
    rhs.append(baseline-degree)
    obj=[int(i<nh) for i in range(nvar)]
    obj[slack]=1000
    matrix=lil_matrix((len(rows),nvar))
    for i,row in enumerate(rows):
        for j,v in row.items():matrix[i,j]=v
    matrix=matrix.tocsr()
    bounds=[(0,1)]*(nvar-1)+[(0,degree)]
    def dual_value(mult):
        # For A*x<=b, p>=0, c*x >= min_box (c+p*A)*x - p*b.
        coeff=[D*v for v in obj]
        offset=0
        for i,p in mult:
            assert type(p) is int and p>=0
            offset-=p*rhs[i]
            for j,v in rows[i].items():coeff[j]+=p*v
        return offset+sum(v*(lo if v>=0 else hi) for v,(lo,hi) in zip(coeff,bounds))
    calls=0
    def visit():
        nonlocal calls
        calls+=1
        if calls>1200:return {'open':True}
        res=linprog(obj,A_ub=matrix,b_ub=rhs,bounds=bounds,method='highs')
        assert res.success
        mult=[[i,int(round(-v*D))] for i,v in enumerate(res.ineqlin.marginals) if -v*D>=0.5]
        if dual_value(mult)>budget*D:return {'dual':mult}
        selected={h for h,i in index.items() if res.x[i]>.5}
        nleft=sum(not set(s)<=selected for s in lead)
        other=sum(not set(s)<=selected for s in supports) if rival else baseline
        if len(selected)<=budget and nleft<=other:
            return {'witness':sorted(selected),'lead':nleft,'challenger':other}
        candidates=[i for i in range(nh) if bounds[i]==(0,1)]
        assert candidates
        i=min(candidates,key=lambda j:abs(.5-res.x[j]))
        children=[]
        for v in (0,1):
            bounds[i]=(v,v)
            child=visit()
            children.append(child)
            if 'witness' in child or 'open' in child:
                bounds[i]=(0,1)
                return child
        bounds[i]=(0,1)
        return {'split':i,'nodes':children}
    cert=visit()
    def verify(t):
        if 'dual' in t:return dual_value(t['dual'])>budget*D
        if 'split' not in t:return False
        i=t['split']
        assert 0<=i<nh and bounds[i]==(0,1) and len(t['nodes'])==2
        for v,child in enumerate(t['nodes']):
            bounds[i]=(v,v)
            assert verify(child)
        bounds[i]=(0,1)
        return True
    certified=verify(cert)
    return dict(degree=baseline,certified=certified,calls=calls,cert=cert)
ordered=sorted((a for a in partners if a!='nvidia'),key=lambda a:(-len(partners[a]),a))
out={}
# Only the largest omitted competitor matters to a rival-free certificate.
for cutoff in (40,32,25,18):
    tail=[a for a in ordered if len(partners[a])<=cutoff]
    residual=case(None,len(partners[tail[0]]))
    if residual['certified']:break
assert residual['certified']
for a in ordered:
    if len(partners[a])<=cutoff:break
    out[a]=case(a,len(partners[a]))
    print(a,out[a]['certified'],out[a]['calls'],flush=True)
report=dict(pin=pin,input_hash=source_sha,degree=degree,cutoff=cutoff,tail_count=len(tail),tail=residual,
    threshold_tested=budget,source_hosts=hosts,certificate_scale=D,scipy=scipy.__version__,rivals=out,all_certified=all(z['certified'] for z in out.values()))
archive=Path('/content/capital-threshold.zip')
with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('result.json',json.dumps(report,sort_keys=True))
print('archive_sha256 '+hashlib.sha256(archive.read_bytes()).hexdigest())
