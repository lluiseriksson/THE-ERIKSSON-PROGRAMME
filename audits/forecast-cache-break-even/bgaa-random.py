"""Certify fixed-workload lower bounds and a mixed-workload randomized latency bound."""
from fractions import Fraction as F
from pathlib import Path
from math import factorial
import json

def band(text):
    half=F(1,2*10**len(text.partition('.')[2]))
    return F(text)-half,F(text)+half

def homogeneous(setup,saving):
    # Buy before service; the activation batch earns its warm saving.
    if saving<=0 or setup<=saving:return F(0)
    k=int(setup//saving)
    premium=setup-saving
    value=k*saving*(premium/setup)**k
    # Optimal first-buy CDF, including the final jump to one.
    cdf=[value/premium*(setup/premium)**j for j in range(k)]+[F(1)]
    assert all(0<=x<=1 for x in cdf) and cdf==sorted(cdf)
    cumulative=F(0)
    for n,p in enumerate(cdf,1):
        cumulative+=p
        regret=setup*p-saving*cumulative-min(0,setup-n*saving)
        assert regret==value
    return value

def row_vertices(row,baseline):
    base,cold,ratio,mult=(band(row[i]) for i in (2,3,4,7))
    low=max(base[0],cold[0]/ratio[1]);high=min(base[1],cold[1]/ratio[0])
    assert low<=high
    points=sorted({low,high}|{c/r for c in cold for r in ratio if low<=c/r<=high})
    for v in points:
        for c in [max(cold[0],ratio[0]*v),min(cold[1],ratio[1]*v)]:
            assert ratio[0]<=c/v<=ratio[1]
            for m in mult:
                for t in baseline:
                    yield v,c,m,t,c-v*m,t-v*m

rows=json.loads(Path('primary.json').read_bytes())['rows']
refs={int(r[0].replace(',','')):band(r[1]) for r in rows if len(r)==3 and r[0].replace(',','').isdigit()}
stats={};best=(F(0),None)
for row in rows:
    if len(row)!=10 or not row[1].replace(',','').isdigit():continue
    if row[0]:model=row[0]
    if model!='Chronos-2':continue
    f=int(row[1].replace(',',''));vs=list(row_vertices(row,refs[f]))
    ss=[a[-1] for a in vs];bb=[a[-2] for a in vs]
    stats[f]=dict(slo=min(ss),shi=max(ss),blo=min(bb),bhi=max(bb))
    for v,c,m,t,B,S in vs:
        val=homogeneous(B,S)
        if val>best[0]:
            best=val,dict(size=f,base=str(v),cold=str(c),warm_ratio=str(m),baseline=str(t),setup=str(B),saving=str(S))
assert len(stats)==7 and min(z['slo'] for z in stats.values())>0
Bmin=min(z['blo'] for z in stats.values());Bmax=max(z['bhi'] for z in stats.values())
rho=max(z['shi']/z['slo'] for z in stats.values());einverse=F(1,sum(F(1,factorial(k)) for k in range(11)))
H=Bmin/(1+(rho-1)*einverse)
U=H*einverse+Bmax-H
assert U==rho*H*einverse+Bmax-Bmin and best[0]<U
print(json.dumps(dict(stats={f:{k:str(v) for k,v in z.items()} for f,z in stats.items()},Bmin=str(Bmin),Bmax=str(Bmax),rho=str(rho),inverse_e_upper=str(einverse),threshold_scale=str(H),upper=str(U),lower=str(best[0]),lower_witness=best[1]),indent=2))