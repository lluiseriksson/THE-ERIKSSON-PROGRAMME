"""Independently evaluate each recorded extremal population using integer mass counts."""
from math import comb
from functools import lru_cache
import json
from pathlib import Path
def read(name):return json.loads(Path(name).read_bytes())
def require(ok,message):
    if not ok:raise ValueError(message)
@lru_cache(maxsize=8192)
def masses(N,A,n):
    return [comb(A,i)*comb(N-A,n-i) if i<=A and n-i<=N-A else 0 for i in range(n+1)]
def witness(row,cut,k,key):
    n,m=row['n'],row['m']
    p=row[key]
    ca=masses(424,p['A'],n)
    cb=masses(259,p['B'],m)
    t=0
    for i,ai in enumerate(ca):
        if not ai:continue
        for j,bj in enumerate(cb):
            if not bj:continue
            full=424*m*i-259*n*j
            # Suppression removes the k largest per-label contributions to rejection.
            nr,ne=i,m-j
            if 424*m>=259*n:
                x=min(k,nr);y=min(k-x,ne)
            else:
                y=min(k,ne);x=min(k-y,nr)
            if full-424*m*x-259*n*y>=cut:t+=ai*bj
    require(t==int(p['numerator']),key)
    return t
a=read('missing.json')
require(a['levels']['0']['rows']==read('power.json')['rows'],'complete-label replication')
for key,level in a['levels'].items():
    k=int(key)
    require([r['n'] for r in level['rows']]==list(range(1,60)),'allocation coverage')
    for r in level['rows']:
        n,m=r['n'],r['m']
        den=comb(424,n)*comb(259,m)
        require(n+m==60 and den==int(r['den']),'sample space')
        cut=r['score']
        prev=max(424*m*i-259*n*j for i in range(n+1) for j in range(m+1) if 424*m*i-259*n*j<cut)
        require(20*witness(r,cut,0,'size')<=den<20*witness(r,prev,0,'previous'),'size boundary')
        if r['delta'] is None:
            require(5*witness(r,cut,k,'power_at_max')<4*den,'infeasible design')
        else:
            require(5*witness(r,cut,k,'one_less')<4*den<=5*witness(r,cut,k,'power'),'power boundary')
    best=min(r['delta'] for r in level['rows'] if r['delta'] is not None)
    require(best==level['best'] and [r['n'] for r in level['rows'] if r['delta']==best]==level['optima'],'optimal allocations')
print(json.dumps({k:[v['best'],v['optima']] for k,v in a['levels'].items()},sort_keys=True))