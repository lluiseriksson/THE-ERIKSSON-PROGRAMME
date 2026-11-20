from pathlib import Path
import csv, io, json, hashlib, zipfile, math
from urllib.request import urlopen
from itertools import combinations
import numpy as np
from scipy.optimize import linprog
url='https://science.nrao.edu/facilities/vla/docs/manuals/obsguide/interp_user_table_0521-166-3c138_2025-03-06.csv'
raw=urlopen(url,timeout=45).read()
digest=hashlib.sha256(raw).hexdigest()
if digest!='ea19cb5f3152e2c4d1514afb9bffe737a77a970b7ee26b664c0bf0a2bd58565e':raise ValueError('Source changed')
rows=list(csv.DictReader(io.StringIO(raw.decode('utf-8-sig'))))
bands=['L','S','C','X','U','K','A','Q']
dates=[r['date'] for r in rows]
if len(set(dates))!=47 or dates!=sorted(dates) or (dates[0],dates[-1])!=('2021-02-01','2024-12-01'):raise ValueError('epoch set')
F=np.array([[float(r[b]) for b in bands] for r in rows])
if np.any(~np.isfinite(F)) or np.any(F<=0):raise ValueError('bad factor')
from fractions import Fraction as Q
from itertools import combinations,permutations
from functools import lru_cache
from collections import Counter
import itertools
X=[[Q(r[b]) for b in bands] for r in rows]
m=len(X);n=len(bands);R=Q(21,19)
cross=X[31][2]/X[31][7]*X[36][7]/X[36][2]
G4=R**2/cross
assert G4>1
@lru_cache(None)
def maxratio(i,j):
    return [[max(X[t][s]/X[t][b] for t in range(i,j+1)) for b in range(n)] for s in range(n)]
@lru_cache(None)
def maybe(i,j):
    # If every simple band cycle is bounded even after maximizing its edges
    # separately, no perturbation can make the date interval infeasible.
    M=maxratio(i,j);scale=G4**2/R**4
    D=[[M[s][t]**4*scale if s!=t else Q(1) for t in range(n)] for s in range(n)]
    for k in range(n):
        for s in range(n):
            for t in range(n):
                alt=D[s][k]*D[k][t]
                if alt>D[s][t]:
                    if s==t:return True
                    D[s][t]=alt
    return False
def first(i):
    low=i;high=m
    while high-low>1:
        h=(low+high)//2
        if maybe(i,h):high=h
        else:low=h
    return high
limits=[first(i) for i in range(m)]
@lru_cache(None)
def chains(i,k):
    if k==1:return [(i,m-1)] if limits[i]<m else []
    return [(i,)+rest for j in range(limits[i],m-k+1) for rest in chains(j,k-1)]
chainlist=chains(0,6)
@lru_cache(None)
def patterns(i,j):
    M=maxratio(i,j);keep={}
    for k in range(2,n+1):
        bound=R**(4*k);free=G4**(2*k)
        for choice in combinations(range(n),k):
            for tail in permutations(choice[1:]):
                nodes=(choice[0],)+tail
                pairs=list(zip(nodes,nodes[1:]+nodes[:1]))
                best=math.prod(M[s][t] for s,t in pairs)
                if best**4*free<=bound:continue
                def visit(q,coef,prod,possible):
                    if q==k:
                        left=tuple(coef.get((i,v),0) for v in range(n));right=tuple(coef.get((j,v),0) for v in range(n))
                        interior=sum(abs(v) for (row,_),v in coef.items() if i<row<j)
                        needed=R**k/prod
                        if G4**(interior+sum(map(abs,left+right)))<=needed**4:return
                        key=(left,right,interior)
                        if key not in keep or needed<keep[key]:keep[key]=needed
                        return
                    s,t=pairs[q];remaining=possible/M[s][t]
                    for row in range(i,j+1):
                        val=X[row][s]/X[row][t]
                        if (prod*val*remaining)**4*free<=bound:continue
                        new=coef.copy();new[row,s]=new.get((row,s),0)+1;new[row,t]=new.get((row,t),0)-1
                        visit(q+1,new,prod*val,remaining)
                visit(0,{},Q(1),best)
    return list(keep.items())
# For every surviving prefix try nonnegative integer combinations of its
# strict inequalities. A failed strict product certifies impossibility.
stats=Counter();trace=[]
def certificate(P,weights):
    co=Counter();need=Q(1);inside=0
    for idx,(left,right,internal,threshold) in enumerate(P):
        w=weights[idx]
        if not w:continue
        need*=threshold**w;inside+=w*internal
        for v in range(n):co[idx,v]+=w*left[v];co[idx+1,v]+=w*right[v]
    return G4**(inside+sum(map(abs,co.values())))<=need**4
def prove(ch,k,P):
    if k==6:raise RuntimeError('Surviving chain needs a stronger exact certificate: '+str(ch))
    i,j=ch[k:k+2]
    for (left,right,internal),needed in patterns(i,j):
        p=P+[(left,right,internal,needed)]
        weights=next((v+(1,) for v in itertools.product((0,1),repeat=k) if certificate(p,v+(1,))),None)
        if weights is None and k==5:
            weights=next((v for v in itertools.product(range(3),repeat=6) if v[-1] and certificate(p,v)),None)
        stats['branches']+=1
        if weights is None:prove(ch,k+1,p)
        else:stats['exact_exclusions']+=1
for ch in chainlist:prove(ch,0,[])
# Common perturbation, checked without logarithms, using actual input decimals.
calendar=[0,12,24,31,36,41,46]
positive=[[0],[1,7],[0],[2],[0,7],[7],[]]
sign={t:[1 if j in cols else -1 for j in range(n)] for t,cols in zip(calendar,positive)}
witness=[]
for h,band in enumerate([0,1,0,2,0,0]):
    i,j=calendar[h:h+2];q=7;rho=X[i][band]*X[j][q]/(X[i][q]*X[j][band])
    z=sign[i][band]-sign[i][q]+sign[j][q]-sign[j][band]
    quotient=rho**4*G4**z/R**8
    assert quotient>=1 and (quotient>1 or z>0)
    witness.append(dict(start=dates[i],end=dates[j],band=bands[band],other=bands[q],slope=z,boundary='equal' if quotient==1 else 'strict'))
# For larger radii use this witness at a sufficiently close smaller radius:
# all strict inequalities persist near G, and each boundary equality grows.
res=dict(source_sha256=digest,fourth_power=str(G4),critical_factor=float(G4)**.25,critical_log_radius=math.log(float(G4))/4,dates=dates,band_order=bands,chains=[list(ch) for ch in chainlist],first_possible_end_index=limits,counts=dict(stats),patterns={str(p):len(patterns(*p)) for ch in chainlist for p in zip(ch,ch[1:])},witness=witness,positive_bands_at_witness_rows={str(t):[bands[k] for k in pos] for t,pos in zip(calendar,positive)},arithmetic='Exact rational source decimals, cycle maxima, dominance pruning, products and exclusion inequalities. Floats only for final display.')
p=Path('/content/archive.zip')
with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('exact.json',json.dumps(res,indent=2))
print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
