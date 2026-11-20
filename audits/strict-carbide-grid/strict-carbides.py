"""Unique compositions and deterministic energy-error margins on an eighth-grid carbide screen."""
from decimal import Decimal as D,getcontext
from math import comb
from itertools import product
import json
getcontext().prec=45
kb=D('1.380649e-23')/D('1.602176634e-19')
def entropy(x):
    return -kb*sum(f*f.ln() for f in x if f)/2
rows=json.load(open('table-s1.json',encoding='utf8'))['rows'];points=[]
for row in rows:
    x=tuple(map(D,row['fractions']));t=D(row['T'])
    if sum(x)!=1 or any(8*v!=int(8*v) for v in x):raise ValueError(row['rank'])
    support=[v for v in x if v!=0];s=entropy(x)
    if abs(t*s-D(row['E']))>D('.00051'):raise ValueError(('normalized energy',row['rank']))
    points.append((row['rank'],x,t,s,len(set(support))==1))
if len({p[1] for p in points})!=100 or any(a[2]>b[2] for a,b in zip(points,points[1:])):raise ValueError('table rank')
strict=[p for p in points if not p[-1]];top=strict[0]
grid={t:comb(6,t)*comb(7,t-1) for t in range(2,7)}
equal={t:comb(6,t) if 8%t==0 else 0 for t in grid}
if sum(v*2**(6-t) for t,v in grid.items())!=7581:raise ValueError('raw multiplicity')
rounding=D('.001')
radii=[]
for rank,x,t,s,_ in strict[1:]:
    den=1/top[3]+1/s
    radii.append(((t-top[2]-rounding)/den,(t-top[2]+rounding)/den,rank))
radii.sort();a,h,j=radii[0]
# Entropy is Schur-concave; the 7/8,1/8 split majorizes every admitted grid vector.
smin=entropy((D(7)/8,D(1)/8))
outside=(points[-1][2]-top[2]-rounding)/(1/top[3]+1/smin)
if h>=min(radii[1][0],outside):raise ValueError('unresolved competitor')
print(json.dumps(dict(grid=grid,equimolar=equal,strict_unique=sum(grid.values())-sum(equal.values()),equal_top100=[p[0] for p in points if p[-1]],best_strict_rank=top[0],best_fractions=list(map(str,top[1])),T=str(top[2]),limiting_rank=j,meV_radius=[str(1000*a),str(1000*h)],other_listed_lower_meV=str(1000*radii[1][0]),unlisted_lower_meV=str(1000*outside)),sort_keys=True))