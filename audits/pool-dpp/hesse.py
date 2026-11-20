"""Exact Eisenstein minor and pool-law checks for the Hesse configuration."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, prod
import json

def require(condition, label):
    if not condition:
        raise ValueError(label)

def mul(u, v):
    a,b = u
    c,d = v
    return a*c-b*d, a*d+b*c-b*d

def detnorm(cols):
    a=b=0
    for perm in permutations(range(3)):
        val=mul(mul(cols[0][perm[0]],cols[1][perm[1]]),cols[2][perm[2]])
        sign=(-1)**sum(perm[i]>perm[j] for i,j in combinations(range(3),2))
        a+=sign*val[0]
        b+=sign*val[1]
    return a*a-a*b+b*b

def columns():
    roots=[(1,0),(0,1),(-1,-1)]
    labels=list(product(range(3),repeat=2))
    result={}
    for a,j in labels:
        z=(0,0);u=(1,0);v=tuple(-x for x in roots[j])
        result[a,j]=[(z,u,v),(v,z,u),(u,v,z)][a]
    return result

def check_geometry(cols):
    norm={}
    for tri in combinations(sorted(cols),3):
        (a,b),(c,d),(e,f)=tri
        area=((c-a)*(f-b)-(d-b)*(e-a))%3
        n=detnorm([cols[z] for z in tri])
        require(n==(3 if area else 0),'Determinant and incidence mismatch')
        norm[tri]=n
    require(Counter(norm.values())=={0:12,3:72},'Minor histogram')
    return {s for s,w in norm.items() if w}

def audit():
    cols=columns()
    support=check_geometry(cols)
    require(all(sum(set(p)<=set(t) for t in support)==6 for p in combinations(cols,2)),'Pair degrees')
    seed=((0,0),(1,0),(0,1))
    orbit=set();maps=0
    for a,b,c,d in product(range(3),repeat=4):
        if (a*d-b*c)%3==0:continue
        for e,f in cols:
            maps+=1
            orbit.add(tuple(sorted((((a*x+b*y+e)%3,(c*x+d*y+f)%3) for x,y in seed))))
    require(maps==432 and orbit==support,'Affine orbit')
    checks=[]
    for n in (3,4,6):
        out=dict.fromkeys(support,Fraction(0));success=0;total=0
        for pool in combinations_with_replacement(sorted(cols),n):
            freq=Counter(pool)
            orders=factorial(n)//prod(factorial(x) for x in freq.values())
            total+=orders
            weights={t:prod(freq[v] for v in t) for t in combinations(sorted(freq),3) if t in support}
            z=sum(weights.values())
            if not z:continue
            success+=orders
            for t,w in weights.items():out[t]+=Fraction(orders*w,z)
        require(total==9**n and total-success==12*3**n-27,'Success law')
        require(set(out.values())=={Fraction(success,72)},'Marginal mass')
        checks.append(dict(N=n,ordered_pools=total,success=success,each_marginal='1/72'))
    bad=cols.copy()
    bad[0,1]=bad[0,0]
    try:check_geometry(bad)
    except ValueError:pass
    else:raise ValueError('Duplicate-column mutation accepted')
    return dict(arithmetic='Z[omega], omega^2=-omega-1',norm_histogram={'0':12,'3':72},
                affine_maps=maps,triangle_orbit=len(orbit),pair_degree=6,enumerations=checks,
                duplicate_column_rejected=True)
if __name__=='__main__':
    print(json.dumps(audit(),sort_keys=True,indent=2))

