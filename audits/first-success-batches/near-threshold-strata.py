from math import comb
from fractions import Fraction as F
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib,json

def mul(p,q):
    a=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): a[i+j]+=x*y
    return a

def power(p,m):
    r=[1]
    for i in range(m):r=mul(r,p)
    return r

def check(n,m,h):
    T=n*m;k=m+h;den=comb(T,k);N=n-1
    ways=power([1]*n,m)
    single=[1]*n
    double=list(range(n-1,0,-1))
    waits=mul(power(single,m-h),power(double,h))
    balanced=F(comb(m,h),den)*sum(F(comb(m+s-1,s)*y,ways[s]) for s,y in enumerate(waits))
    qrows=[comb(m+s-1,s)*comb(m*N-s,h) for s in range(m*N+1)]
    assert sum(qrows)==den
    L=2*N*h
    if h<=F(m,8):
        pR=F(sum(v for s,v in enumerate(qrows) if m*N-s>=L),den)
        end_fails=F(comb(T-L,k),den)
        assert pR>=end_fails>=F(1,4)**L
        assert balanced>=pR*F(1,2)**h
    collision=1-balanced
    assert collision<=F(h*(h-1),m+1)
    return dict(n=n,m=m,h=h,balanced=str(balanced))

def main():
    cases=[check(n,m,h) for n in range(2,6) for m in range(2,13) for h in range(1,m+1)]
    examples=[]
    for n,m in [(2,1000000),(3,1000000),(4,1000000),(5,100000000)]:
        # ln(2)<1 and ln(T+1)<=bit_length(T+1); rational sufficient bounds.
        h=m//(16*n**n*(4*n-3))
        assert h>=1 and h<=min(F(m,8),F(m,2*n**n))
        assert (m*n+1).bit_length()+h*(4*n-3)<=F(m,8*n**n)
        examples.append([n,m,h])
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('band.json',json.dumps(dict(checked=len(cases),exact=cases,examples=examples)))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
