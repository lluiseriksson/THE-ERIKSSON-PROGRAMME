"""Witness generator for simultaneous lower bounds on shortlist misses.
Run under Python 3. Supply exact positive weights and one cutoff per strategy.
"""
from fractions import Fraction as F
from itertools import permutations, product
import json

def energy(p):
    return sum((i - x) ** 2 for i, x in enumerate(p)) // 2

def misses(p, k):
    return sum(x >= k for x in p[:k])

def least(n, k, d):
    if not 0 <= d <= min(k, n-k):
        raise ValueError("infeasible cutoff or deficit")
    p = list(range(n))
    p[k-d:k+d] = p[k:k+d] + p[k-d:k]
    return p

def witness(n, claims, r):
    """claims are (positive integer weight, cutoff, required misses). Half-up rounding."""
    W = sum(w for w, k, d in claims)
    assert W > 0 and all(w > 0 for w, k, d in claims)
    C = F(n*(n*n-1), 12)
    lower = W*C*(1-r-F(1,200))
    upper = W*C*(1-r+F(1,200))
    assert (n-1)*max(w for w,k,d in claims) <= upper-lower
    rows = [least(n,k,d) for w,k,d in claims]
    cost = sum(w*d**3 for w,k,d in claims)
    if cost > upper:
        return None
    for p,(w,k,d) in zip(rows,claims):
        while cost <= lower:
            pos = next((i for i in range(n-1) if p[i] < p[i+1]), None)
            if pos is None:
                break
            delta = p[pos+1]-p[pos]
            p[pos],p[pos+1] = p[pos+1],p[pos]
            cost += w*delta
        if cost > lower:
            break
    assert lower < cost <= upper
    assert sum(w*energy(p) for p,(w,k,d) in zip(rows,claims)) == cost
    assert all(sorted(p)==list(range(n)) and misses(p,k)>=d for p,(w,k,d) in zip(rows,claims))
    return dict(total_energy=cost, actual_mean=str(1-F(cost,W)/C),rankings=rows)

def verify():
    # Exhaustively verify the minimum cost and the step identity on small rankings.
    small=0
    for n in range(2,9):
        minima={}
        for p in permutations(range(n)):
            E=energy(p)
            for k in range(1,n):
                key=(k,misses(p,k));minima[key]=min(minima.get(key,E),E)
            for i in range(n-1):
                if p[i]<p[i+1]:
                    q=list(p);q[i],q[i+1]=q[i+1],q[i]
                    assert energy(q)-E==p[i+1]-p[i]
                    assert misses(q,i+1)>=misses(p,i+1)
            small+=1
        assert all(E==d**3 for (k,d),E in minima.items())
    cases={}
    for label in ['0.70','0.73']:
        r=F(label)
        for weights in [[1]*10,[1,2,3,4,5],[1,19]]:
            for k in [15,16,20,27]:
                d=k
                W=sum(weights);U=W*13860*(1-r+F(1,200))
                count=max(i for i in range(len(weights)+1) if sum(weights[:i])*d**3<=U)
                claims=[(w,k,d if i<count else 0) for i,w in enumerate(weights)]
                got=witness(55,claims,r)
                assert got is not None and sum(misses(p,k)==k for p in got['rankings'])==count
                if count<len(weights):
                    assert witness(55,[(w,k,d if i<=count else 0) for i,w in enumerate(weights)],r) is None
                cases[f'{label}:{weights}:{k}']=dict(maximum=count,**got)
        mixed=[(1,6,2),(2,20,12),(4,27,15),(5,35,14)]
        cases[label+':mixed']=witness(55,mixed,r)
    print(json.dumps(dict(exhaustive_permutations=small,cases=cases)))
if __name__=='__main__':
    verify()