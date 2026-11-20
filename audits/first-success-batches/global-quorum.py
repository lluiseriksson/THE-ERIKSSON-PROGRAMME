"""Expected inspection cost of a shuffled exact decision on a fixed candidate bank."""
from collections import Counter
from fractions import Fraction
from itertools import combinations,product
from math import comb
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib,json

COUNTS=[80, 97, 66, 19, 33, 84, 93, 88, 95, 26, 95, 82, 99, 97, 92, 92, 33, 100, 69, 100, 76, 59, 88, 70, 51, 80, 71, 78, 71, 97, 86, 61, 70, 96, 15, 100, 45, 82, 8, 98, 65, 1, 77, 83, 97, 88, 99, 23, 93, 80, 66, 51, 100, 94, 71, 80, 63, 99, 78, 99, 100, 98, 94, 100, 97, 24, 29, 26, 44, 71, 100, 100, 100, 100, 100, 47, 2, 94, 73, 95, 100, 9, 7, 57, 45, 87, 100, 7, 93, 82, 66, 98, 57, 88, 98, 100, 100, 94, 93, 30, 27, 67, 89, 59, 100, 99, 96, 4, 92, 78, 97, 97, 100, 4, 100, 86, 99, 97]

def cost(t,h,m):
    if h>=m:
        return Fraction(m*(t+1),h+1)
    return Fraction((t-m+1)*(t+1),t-h+1)

def brute(t,h,m):
    total=0
    for success in combinations(range(t),h):
        s=f=0
        for j in range(t):
            if j in success:s+=1
            else:f+=1
            if s==m or f==t-m+1:break
        total+=j+1
    return Fraction(total,comb(t,h))

def run(counts,d,replace):
    den=d*d if replace else d*(d-1)
    weights=[1]
    for c in counts:
        q=d-c
        one=[q*(q if replace else q-1),2*q*c,c*(c if replace else c-1)]
        update=[0]*(len(weights)+2)
        for i,x in enumerate(weights):
            for j,y in enumerate(one):update[i+j]+=x*y
        weights=update
    m=len(counts)
    if sum(weights)!=den**m:raise ValueError("mass")
    expected=sum(w*cost(2*m,h,m) for h,w in enumerate(weights))/den**m
    stopped=m+Fraction(sum(d-c for c in counts),d)
    return dict(cost_global=str(expected),global_approx=float(expected),cost_first_hit=str(stopped),
                first_hit_approx=float(stopped),full_cost=2*m,
                miss=str(Fraction(sum(weights[:m]),den**m)))
checks=0
for t in range(1,10):
    for h in range(t+1):
        for m in range(1,t+1):
            if cost(t,h,m)!=brute(t,h,m):raise ValueError((t,h,m))
            checks+=1
rows=[dict(panel=panel,replacement=r,**run(counts,100,r))
      for panel,counts in [('all',COUNTS),('mixed',[v for v in COUNTS if 0<v<100])] for r in [True,False]]
p=Path('/content/archive.zip')
with ZipFile(p,'w',ZIP_DEFLATED) as z:
    z.writestr('quorum.json',json.dumps(dict(tests=checks,rows=rows),sort_keys=True))
print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())

