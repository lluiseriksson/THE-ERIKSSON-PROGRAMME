from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, prod, lcm
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib, json

def ordered(m,n):
    # Scale the stopped mean and full tail by the same positive odds denominator.
    waits=list(product(range(n),repeat=m))
    multiplicity=Counter(map(sum,waits))
    weights={s:F(comb(m-1+s,m-1),v) for s,v in multiplicity.items()}
    scale=lcm(*(v.denominator for v in weights.values()))
    terms=Counter()
    for k in product(range(n+1),repeat=m):
        if sum(k)>=m:
            terms[k]=scale*prod(comb(n,t) for t in k)
    for u in waits:
        score=int(scale*weights[sum(u)])
        for t in product(*(range(n-v) for v in u)):
            terms[tuple(j+1 for j in t)]-=score*prod(comb(n-1-v,j) for v,j in zip(u,t))
    # Substitute odds_i = gap_1 + ... + gap_i without negative coefficients in these linear forms.
    @lru_cache(None)
    def power(i,k):
        if k==0:return {(0,)*m:1}
        out=Counter()
        for mon,c in power(i,k-1).items():
            for h in range(i+1):
                t=list(mon);t[h]+=1;out[tuple(t)]+=c
        return out
    summed=Counter()
    for mon,c in terms.items():
        if not c:continue
        partial={(0,)*m:c}
        for i,k in enumerate(mon):
            next_terms=Counter()
            for x,v in partial.items():
                for y,w in power(i,k).items():
                    next_terms[tuple(a+b for a,b in zip(x,y))]+=v*w
            partial=next_terms
        summed.update(partial)
    surviving=sorted((k,v) for k,v in summed.items() if v)
    # Re-evaluate independently against both probability laws at integer odds.
    for odds in [(1,)*m,tuple(range(1,m+1)),tuple(range(m))]:
        gaps=(odds[0],)+tuple(b-a for a,b in zip(odds,odds[1:]))
        denom=prod((1+x)**n for x in odds)
        full=sum(prod(comb(n,t)*x**t for x,t in zip(odds,k)) for k in product(range(n+1),repeat=m) if sum(k)>=m)
        mean=sum(weights[sum(u)]*prod(F(x,(1+x)**(1+v)) for x,v in zip(odds,u)) for u in waits)
        recovered=sum(c*prod(x**t for x,t in zip(gaps,k)) for k,c in surviving)
        assert recovered==scale*(full-denom*mean)
    return dict(m=m,n=n,scale=scale,terms=surviving,negative=sum(v<0 for _,v in surviving),
        diagonal_survivors=sum(all(j==0 for j in k[1:]) for k,v in surviving))

def main():
    rows=[ordered(3,n) for n in (3,4,5)]+[ordered(4,3)]
    path=Path('/content/archive.zip')
    with ZipFile(path,'w',ZIP_DEFLATED) as z:z.writestr('ordered.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=='__main__':main()
