"""Exact finite-population costs for a prespecified discrepancy threshold."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb
import json

def choose(n,k):
    return comb(n,k) if 0<=k<=n else 0

@lru_cache(maxsize=50000)
def mass(N,k,n,x):
    # Count the smaller of the two equivalent placement / draw experiments.
    if k<n:
        return Fraction(choose(n,x)*choose(N-n,k-x),comb(N,k))
    return Fraction(choose(k,x)*choose(N-k,n-x),comb(N,n))

def event(N,k,n,S,q,m,d):
    return sum(mass(N,k,n,x)*mass(S,S-q,m,y) for x in range(d+1) for y in range(d+1-x))

def frontier(endpoint,tolerance):
    N,S,B=2062,27,24
    def hidden(q):
        target=q if endpoint=='count' else (2086*q+71)//72
        return max(0,target-B)
    def worst(n,m):
        return max((event(N,hidden(q),n,S,q,m,tolerance),q) for q in range(S+1))
    rows=[]
    for m in range(S+1):
        if worst(N,m)[0]>Fraction(1,20):continue
        lo,hi=-1,N
        while hi-lo>1:
            n=(hi+lo)//2
            if worst(n,m)[0]<=Fraction(1,20):hi=n
            else:lo=n
        p,q=worst(hi,m)
        previous=worst(hi-1,m)[0] if hi else None
        assert p<=Fraction(1,20) and (previous is None or previous>Fraction(1,20))
        rows.append(dict(before=hi,after=m,total=hi+m,worst_q=q,risk=str(p),risk_float=float(p),risk_one_fewer_before=str(previous)))
    if not rows:return dict(frontier=[],optima=[])
    minimum=min(r['total'] for r in rows)
    return dict(frontier=rows,optima=[r for r in rows if r['total']==minimum])

def small_checks():
    checks=0
    N,S,B=5,3,1
    for n in range(N+1):
        samples=list(combinations(range(N),n))
        for m in range(S+1):
            posts=list(combinations(range(S),m))
            for d in (0,1):
                for q in range(S+1):
                    for k in range(N+1):
                        hits=sum(sum(i<k for i in sample)+sum(i>=q for i in post)<=d for sample in samples for post in posts)
                        assert Fraction(hits,len(samples)*len(posts))==event(N,k,n,S,q,m,d)
                        checks+=1
                for scale in (1,2):
                    all_null=max(event(N,k,n,S,q,m,d) for q in range(S+1) for k in range(N+1) if B+k>=scale*q)
                    edge=max(event(N,max(0,scale*q-B),n,S,q,m,d) for q in range(S+1) if scale*q<=B+N)
                    assert all_null==edge
    return checks

if __name__=='__main__':
    print(json.dumps(dict(small_checks=small_checks(),designs={f'{endpoint}-{d}':frontier(endpoint,d) for endpoint in ('count','yield') for d in (0,1)}),indent=2))