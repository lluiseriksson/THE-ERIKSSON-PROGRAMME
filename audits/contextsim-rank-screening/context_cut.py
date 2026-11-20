"""Tie-free Spearman benchmark. Witnesses are synthetic permutations, not A/B data."""
from fractions import Fraction as F
from itertools import permutations,product
import json
n=55;C=n*(n*n-1)//12
def energy(p):
    s=sum((i-j)**2 for i,j in enumerate(p));assert s%2==0
    return s//2
def full(m):return m*(m*m-1)//6
little={m:{energy(p):list(p) for p in permutations(range(m))} for m in range(5)}
assert set(little[4])==set(range(full(4)+1))
def realize(m,v):
    if m<=4:return little[m][v]
    if v<=full(m-1):return realize(m-1,v)+[m-1]
    return [m-1]+realize(m-1,v-m*(m-1)//2)
def make(k,d,E):
    sizes=[k-d,d,d,n-k-d]
    # Allocate extra energy to independent permutations within the four blocks.
    # Sizes <=3 have possible gaps; large blocks have full integer energy ranges.
    small=[i for i,m in enumerate(sizes) if m<=3];big=[i for i,m in enumerate(sizes) if m>=4]
    for z in product(*(little[sizes[i]].keys() for i in small)):
        rest=E-d**3-sum(z)
        if not 0<=rest<=sum(full(sizes[i]) for i in big):continue
        values=dict(zip(small,z))
        for i in big:
            values[i]=min(rest,full(sizes[i]));rest-=values[i]
        assert rest==0
        offsets=[0,k,k-d,k+d]
        p=[off+v for i,(m,off) in enumerate(zip(sizes,offsets)) for v in realize(m,values[i])]
        assert sorted(p)==list(range(n)) and energy(p)==E and len(set(range(k))&set(p[:k]))==k-d
        return p
    return None
out={}
for s in ['0.73','0.70']:
    label=F(s);E=round((1-label)*C);rho=1-F(E,C)
    lo=label-F(1,200);lim=(1-lo)*C
    assert abs(rho-label)<F(1,200)
    rows={}
    for k in range(1,n+1):
        d=max(d for d in range(min(k,n-k)+1) if d**3<=lim)
        worst=make(k,d,E);best=make(k,0,E)
        assert worst is not None and best is not None,(s,k,d)
        rows[k]=dict(minimum=k-d,maximum=k,min_permutation=worst,max_permutation=best)
    out[s]=dict(energy=E,actual_rho=str(rho),cutoffs=rows)
print(json.dumps(out))
