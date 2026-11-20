"""Check relative probabilities of labelled suffix-hit allocations on full count strata."""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile
import hashlib
import json

@lru_cache(maxsize=24)
def empty_sites(m, n):
    a = [1]
    for _ in range(m):
        prefix = [0]
        for v in a:
            prefix.append(prefix[-1]+v)
        a = [prefix[min(j+1,len(a))]-prefix[max(0,j-n+1)] for j in range(len(a)+n-1)]
    return a

def relative(m,n,h,nonzero):
    assert h==sum(nonzero) and all(1<=e<n for e in nonzero)
    total=m*n
    ways=comb(total,m+h)
    uncapped=comb(m+h-1,h)
    denom=empty_sites(m,n)
    a=empty_sites(m-len(nonzero),n)
    for e in nonzero:
        poly=[comb(e+j,e) for j in range(n-e)]
        nxt=[0]*(len(a)+len(poly)-1)
        for j,c in enumerate(poly):
            for i,v in enumerate(a):
                nxt[j+i]+=c*v
        a=nxt
    scale=10**17
    lower=upper=0
    for j,v in enumerate(a):
        slots=j+h
        num=scale*uncapped*comb(total-slots-1,m-1)*v
        div=ways*denom[slots]
        q,rem=divmod(num,div)
        lower+=q
        upper+=q+bool(rem)
    return lower,upper,scale

def brute(m,n,h,e):
    mass=Fraction()
    for bits in product(range(2),repeat=m*n):
        blocks=[bits[i*n:(i+1)*n] for i in range(m)]
        if [sum(x)-1 for x in blocks]!=list(e):continue
        s=sum(x.index(1) for x in blocks)
        mass+=Fraction(comb(m+s-1,s),empty_sites(m,n)[s])
    return mass*comb(m+h-1,h)/comb(m*n,m+h)

def main():
    rows=[]
    for m,n,h in [(3,3,2),(8,2,2),(16,3,2),(128,3,2),(1024,3,2),
                  (16,3,4),(64,3,8),(256,3,16),(1024,3,32),(81,4,9)]:
        patterns=[[1]*h]
        if h%(n-1)==0 and n>2:patterns.append([n-1]*(h//(n-1)))
        for e in patterns:
            lo,hi,sc=relative(m,n,h,e)
            assert 0<lo<=hi and hi-lo<=m*(n-1)+1
            if m==3:
                exact=brute(m,n,h,e+[0]*(m-len(e)))
                assert lo<=exact*sc<=hi
            if n==2:
                exact=Fraction(comb(m+h-1,h),comb(m,h))
                assert lo<=exact*sc<=hi
            rows.append(dict(m=m,n=n,h=h,profile=e,lower=lo,upper=hi,scale=sc))
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:
        z.writestr('allocation.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())

if __name__=='__main__':main()
