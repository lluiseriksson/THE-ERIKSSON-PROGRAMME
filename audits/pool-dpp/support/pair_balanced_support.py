"""Find a pair-balanced incomplete triple catalog with bias at pool size four."""
from fractions import Fraction
from itertools import combinations
from math import comb
import json

def require(ok, message):
    if not ok:
        raise ValueError(message)

def audit(d, blocks):
    pairs=list(combinations(range(d),2))
    degrees={pair:sum(set(pair)<=set(t) for t in blocks) for pair in pairs}
    require(len(set(degrees.values()))==1,'Pair degrees differ')
    totals={s:Fraction(0) for s in blocks}
    # Direct counts of ordered pools up to permutation, at N=4.
    # The three-distinct-label patterns occur in 3*4!/2! = 36 orders
    # for a given supported triple. A four-distinct window occurs in 24.
    numerator={s:Fraction(36) for s in blocks}
    success=36*len(blocks)
    for window in combinations(range(d),4):
        hits=[t for t in combinations(window,3) if t in blocks]
        if not hits:
            continue
        success+=24
        for t in hits:
            numerator[t]+=Fraction(24,len(hits))
    law={s:w/success for s,w in numerator.items()}
    require(sum(law.values())==1,'Probability mass lost')
    if len(set(law.values()))==1:
        return
    # A separate enumeration counts individual ordered label sequences,
    # weighting each by the exact number of supported occurrence triples.
    from itertools import product
    success2=0
    for pool in product(range(d),repeat=4):
        hit=[]
        for i,j,k in combinations(range(4),3):
            t=tuple(sorted((pool[i],pool[j],pool[k])))
            if t in blocks:
                hit.append(t)
        if hit:
            success2+=1
            for t in hit:
                totals[t]+=Fraction(1,len(hit))
    require(success==success2 and all(law[t]==totals[t]/success for t in law),'Direct ordered pool discrepancy')
    return dict(catalog_size=d,blocks=[list(s) for s in sorted(blocks)],pair_degree=next(iter(degrees.values())),
                target=str(Fraction(1,len(blocks))),success=success,total_pools=d**4,
                marginal={','.join(map(str,t)):str(law[t]) for t in sorted(law)})

def search():
    for d in (6,7,8,9,10,11,12,13):
        triples=set(combinations(range(d),3))
        orbits=[]
        while triples:
            t=min(triples)
            orbit=frozenset(tuple(sorted((i+a)%d for i in t)) for a in range(d))
            triples-=orbit
            orbits.append(orbit)
        pairs=[(0,j) for j in range(1,1+d//2)]
        inc=[[sum(set(pair)<=set(t) for t in orbit) for pair in pairs] for orbit in orbits]
        for m in range(2,min(6,len(orbits))+1):
            for ix in combinations(range(len(orbits)),m):
                partial=[sum(inc[a][j] for a in ix) for j in range(len(pairs))]
                if len(set(partial))!=1:
                    continue
                hit=audit(d,set().union(*(orbits[i] for i in ix)))
                if hit:
                    hit['generators']=[list(min(orbits[i])) for i in ix]
                    return hit
    raise ValueError('No asymmetric law in the bounded cyclic search')
if __name__=='__main__':
    print(json.dumps(search(),sort_keys=True,indent=2))
