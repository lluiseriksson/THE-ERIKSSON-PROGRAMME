"""Reproduce matched panel shapes and post-hoc event-paired bootstrap uncertainty."""
from pathlib import Path
from io import BytesIO
from urllib.parse import urlsplit,parse_qs
from itertools import combinations
import hashlib,sys,subprocess,zipfile,json
import numpy as np
import pandas as pd
HASH='19a1ed759ab2b2f05a9a0bba63825c83ceccf90a1932b60974c796437b2650fc'
def acquire():
    if Path('osf-source.zip').exists():return Path('osf-source.zip').read_bytes()
    import requests
    try:from pypdf import PdfReader
    except ImportError:
        subprocess.run([sys.executable,'-m','pip','install','--quiet','pypdf==5.9.0'],stdout=sys.stderr,check=True,timeout=90)
        from pypdf import PdfReader
    session=requests.Session()
    pdf=session.get('https://aclanthology.org/2026.finnlp-1.30.pdf',timeout=25);pdf.raise_for_status()
    links={str(a.get_object().get('/A',{}).get('/URI','')) for p in PdfReader(BytesIO(pdf.content)).pages for a in p.get('/Annots',[])}
    u,=[urlsplit(v) for v in links if urlsplit(v).hostname=='osf.io'];q=parse_qs(u.query)
    node=session.get('https://api.osf.io/v2/nodes/8u5hc/files/osfstorage/',params=q,timeout=25)
    if node.status_code!=200:raise ValueError(('OSF metadata HTTP',node.status_code))
    f,=[f for f in node.json()['data'] if f['id']=='6a7af69aad7e2cb62d692ab1']
    link=f['links']['download'];d=session.get(link,params=q if 'view_only=' not in link else None,timeout=60)
    if d.status_code!=200:raise ValueError(('OSF archive HTTP',d.status_code))
    return d.content
def maskshape(indices):
    return ''.join(map(str,sorted([sum(i//2==g for i in indices) for g in range(3)],reverse=True)))
raw=acquire()
if hashlib.sha256(raw).hexdigest()!=HASH:raise ValueError('Source archive hash')
archive=zipfile.ZipFile(BytesIO(raw))
manifest=pd.read_csv(archive.open('results/paper/strict_market_manifest.csv'),dtype={'market_id':str,'event_id':str})
manifest=manifest[manifest.temporal_status=='strict_pre_end'].sort_values('market_id')
if len(manifest)!=609 or manifest.market_id.nunique()!=609 or manifest.event_id.isna().any():raise ValueError('Cohort')
mids=manifest.market_id.tolist();y=manifest.y.to_numpy()
shapes={}
for k in range(1,7):
    for s in combinations(range(6),k):shapes.setdefault(maskshape(s),[]).append(s)
rng=np.random.default_rng(20261120);output={};vectors=[]
for name,tag,floor,printed in [('GPT','full708',3,-0.00486),('Qwen','qwen_iface',1,-0.01101),('OLMo','olmo708',3,-0.00418)]:
    fc=pd.read_parquet(BytesIO(archive.read('results/forecasts/'+tag+'_forecasts.parquet')),columns=['market_id','condition','articles','agent_idx','probability_yes'])
    fc.market_id=fc.market_id.astype(str);fc=fc[fc.market_id.isin(mids)&fc.condition.isin(['C1','C3'])]
    base=[];routed=[]
    for mid in mids:
        group=fc[fc.market_id==mid]
        g1=group[group.condition=='C1'];g3=group[group.condition=='C3']
        if len(g1)!=6 or len(g3)!=6 or g1.agent_idx.nunique()!=6 or g3.agent_idx.nunique()!=6:raise ValueError('Member identities')
        if len({tuple(sorted(a)) for a in g1.articles})!=1:raise ValueError('Shared pair')
        buckets={}
        for row in g3.itertuples():buckets.setdefault(tuple(sorted(row.articles)),[]).append(float(row.probability_yes))
        if sorted(map(len,buckets.values()))!=[2,2,2]:raise ValueError('Routed pair counts')
        base.append(g1.probability_yes.mean());routed.append([p for key in sorted(buckets) for p in buckets[key]])
    base=np.array(base);P=np.array(routed)
    if not np.isfinite(P).all() or not np.isfinite(base).all():raise ValueError('Missing member')
    losses={}
    for key,subsets in shapes.items():
        losses[key]=np.mean([(P[:,idx].mean(axis=1)-y)**2 for idx in subsets],axis=0)-(base-y)**2
    if abs(losses['222'].mean()-printed)>0.0000051:raise ValueError(('Primary contrast',name))
    # Maximize conditional expected loss per market before averaging across contracts.
    eligible=[v for k,v in losses.items() if sum(map(int,k))>=floor]
    worst=np.max(np.stack(eligible),axis=0);vectors.append(worst)
    output[name]={'minimum_retained':floor,'full_panel_delta':float(losses['222'].mean()),'same_two_vs_full':float(losses['200'].mean()),'fixed_means':{k:float(v.mean()) for k,v in losses.items()},'worst_mean':float(worst.mean()),'contracts_positive':int(sum(worst>1e-12))}
# Resample whole parent events, keeping every condition and endpoint paired.
_,codes=np.unique(manifest.event_id.to_numpy(),return_inverse=True)
n=codes.max()+1;counts=np.bincount(codes);mat=np.column_stack([np.bincount(codes,weights=v) for v in vectors])
rep=[]
for batch in range(100):
    ids=rng.integers(0,n,size=(100,n));rep.append(mat[ids].sum(axis=1)/counts[ids].sum(axis=1)[:,None])
boot=np.vstack(rep)
for j,name in enumerate(output):
    output[name]['paired_percentile_95']=np.quantile(boot[:,j],[.025,.975]).tolist()
    output[name]['bonferroni_upper_95_three']=float(np.quantile(boot[:,j],1-.05/3))
print(json.dumps(dict(source_sha256=HASH,markets=len(mids),events=int(n),draws=len(boot),seed=20261120,results=output),indent=2))
