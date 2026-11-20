"""Exact near-full strata with a fixed group of named tasks."""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
from math import comb
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json


def choose(n,k):
    return comb(n,k) if 0<=k<=n else 0


@lru_cache(None)
def cap(m,n,s):
    return sum((-1)**j*choose(m,j)*comb(m+s-n*j-1,m-1) for j in range(min(m,s//n)+1))


def audit(m,n,r,f,positive_endpoint=True):
    full=[0]*(r*n+1)
    weighted=[F(0)]*len(full)
    exhausted=[0]*len(full)
    rest=m-r
    for y in range(min(r*n,f)+1):
        allowed_group=0
        for u in range(min(y,r*(n-1))+1):
            prefix_group=cap(r,n,u)*choose(r*(n-1)-u,y-u)
            allowed_group+=prefix_group
            for v in range(min((n-1)*rest,f-y)+1):
                if prefix_group==0:continue
                prefix_rest=cap(rest,n,v)*choose(rest*(n-1)-v,f-y-v)
                weight=F(comb(m+u+v-1,u+v),cap(m,n,u+v))
                weighted[y]+=prefix_rest*prefix_group*weight
        suffix=choose(rest*n,f-y)
        full[y]=choose(r*n,y)*suffix
        exhausted[y]=(choose(r*n,y)-allowed_group)*suffix
    assert sum(full)==sum(weighted)==comb(m*n,f)
    assert sum(j*(a-b) for j,(a,b) in enumerate(zip(full,weighted)))==0
    ratios=[]
    for h in range(1,r*n):
        gap=sum((y-h)*(full[y]-weighted[y]) for y in range(h+1,r*n+1))
        lead=sum((y-h)*exhausted[y] for y in range(h+1,r*n+1))
        if lead:
            if positive_endpoint:
                assert gap>0
            ratios.append(gap/lead)
        else:assert gap==0
    return full,weighted,dict(tasks=m,cap=n,named=r,failures=f,nonzero=len(ratios),
             ratio_min=float(min(ratios)) if ratios else None,ratio_max=float(max(ratios)) if ratios else None)


def exhaustive(m,n,r,f):
    out=[F(0)]*(r*n+1); counts=[0]*len(out)
    for bits in product((0,1),repeat=m*n):
        if sum(bits)!=f:continue
        y=sum(bits[:r*n]);counts[y]+=1
        blocks=[bits[i:i+n] for i in range(0,m*n,n)]
        if all(0 in part for part in blocks):
            s=sum(part.index(0) for part in blocks)
            out[y]+=F(comb(m+s-1,s),cap(m,n,s))
    return counts,out


def main():
    rows=[]
    for n in (3,4,6):
        for r in (1,2,3):
            for m in (16,64,256,1024):
                for f in (n-1,n,2*n,4*n):
                    rows.append(audit(m,n,r,f)[2])
    brute=0
    for m,n,r in ((3,3,1),(3,3,2),(4,3,2),(3,4,2)):
        for f in range((n-1)*m+1):
            assert audit(m,n,r,f,positive_endpoint=False)[:2]==exhaustive(m,n,r,f)
            brute+=1
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:
        z.writestr('group-endpoint.json',json.dumps(dict(brute=brute,rows=rows)))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())


if __name__=='__main__': main()
