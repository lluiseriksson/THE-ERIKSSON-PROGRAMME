"""Certify homogeneous success-count convex order, for one named task."""
from functools import lru_cache
from itertools import product
from fractions import Fraction
from math import comb
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json


@lru_cache(None)
def capped(m,n):
    if m==0: return (1,)
    old=capped(m-1,n)
    new=[0]*(len(old)+n-1)
    for i,v in enumerate(old):
        for j in range(n): new[i+j]+=v
    assert sum(new)==n**m
    return tuple(new)


def certificate(m,n):
    T=m*n
    L=T-m
    # Rounding outward weights brackets every labelled sum, without
    # requiring an lcm of all capped-composition counts.
    scale=1<<(T+40)
    whole=capped(m,n)
    smaller=capped(m-1,n)
    weights=[divmod(comb(m+s-1,s)*scale,c) for s,c in enumerate(whole)]
    lo=[[0]*(T+1) for _ in range(n+1)]
    hi=[[0]*(T+1) for _ in range(n+1)]
    for v,c in enumerate(smaller):
        free=(m-1)*(n-1)-v
        rest=[comb(free,i) for i in range(free+1)]
        for j in range(1,n+1):
            lower=upper=0
            for u in range(n-j+1):
                ways=c*comb(n-u-1,j-1)
                q,rem=weights[v+u]
                lower+=ways*q
                upper+=ways*(q+bool(rem))
            for i,b in enumerate(rest):
                k=m+j-1+i
                lo[j][k]+=lower*b
                hi[j][k]+=upper*b
    count=zero=0
    for k in range(m,T+1):
        actual=[comb(n,j)*comb(T-n,k-j)*scale if 0<=k-j<=T-n else 0 for j in range(n+1)]
        total=comb(T,k)*scale
        assert sum(lo[j][k] for j in range(n+1))<=total<=sum(hi[j][k] for j in range(n+1))
        assert sum(j*lo[j][k] for j in range(n+1))*m<=k*total<=sum(j*hi[j][k] for j in range(n+1))*m
        for h in range(1,n):
            # If fewer than n failures occur the score equals one pointwise.
            # A hinge is also affine on both supports when R >= h.
            if T-k<n or k-(T-n)>=h:
                zero+=1
                continue
            lower=sum((j-h)*(actual[j]-hi[j][k]) for j in range(h+1,n+1))
            upper=sum((j-h)*(actual[j]-lo[j][k]) for j in range(h+1,n+1))
            if upper==lower==0:
                zero+=1
                continue
            if lower<=0: raise ValueError((m,n,k,h,lower,upper))
            count+=1
    return dict(tasks=m,cap=n,positive=count,equal=zero)


def direct(m,n):
    c=capped(m,n)
    w=[Fraction(comb(m+s-1,s),a) for s,a in enumerate(c)]
    z={}
    for row in product((0,1),repeat=m*n):
        k=sum(row)
        if k<m: continue
        pieces=[row[i:i+n] for i in range(0,m*n,n)]
        score=w[sum(p.index(1) for p in pieces)] if all(any(p) for p in pieces) else 0
        for h in range(1,n):
            key=(k,h)
            z[key]=z.get(key,0)+(1-score)*max(0,sum(pieces[0])-h)
    assert min(z.values())>=0
    return sum(v>0 for v in z.values()),sum(v==0 for v in z.values())


def main():
    rows=[]
    for n,limit in ((4,64),(5,36),(6,25),(8,14),(12,8)):
        for m in range(2,limit+1):
            r=certificate(m,n)
            if m*n<=16:
                assert direct(m,n)==(r['positive'],r['equal'])
            rows.append(r)
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:
        z.writestr('hinges.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())


if __name__=='__main__':main()
