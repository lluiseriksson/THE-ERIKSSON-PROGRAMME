"""Finite certificates in the proof of the universal two-extra-success stratum."""
from itertools import product
from math import comb
from fractions import Fraction
from pathlib import Path
import hashlib,json,zipfile


def no_triples(n,m):
    k=m+2
    return sum(comb(m,j)*comb(m-j,k-2*j)*comb(n,2)**j*n**(k-2*j) for j in range(2,k//2+1))


def polynomial(n,m):
    total=comb(n*m,m+2)
    return (m-1)*total-(m+1)*no_triples(n,m)


def differences(m):
    start=4 if m==4 else 3
    a=[polynomial(n,m) for n in range(start,start+m+4)]
    ds=[]
    while a:
        ds.append(a[0])
        a=[y-x for x,y in zip(a,a[1:])]
    assert ds[-1]==0 and all(x>=0 for x in ds)
    for n in (start,start+1,25,103,1000):
        assert sum(x*comb(n-start,i) for i,x in enumerate(ds))==polynomial(n,m)
    return dict(m=m,origin=start,coefficients=ds[:-1])


def special():
    # m=4,n=3: enumerate the complete stratum, grouped by counts.
    m,n,k=4,3,6
    ways=[0]*(m*(n-1)+1)
    for u in product(range(n),repeat=m):ways[sum(u)]+=1
    any_triple=0
    weighted_triple=Fraction()
    for paths in product(range(1<<n),repeat=m):
        r=[p.bit_count() for p in paths]
        if sum(r)!=k or max(r)<3:continue
        any_triple+=1
        if all(paths):
            s=sum((p&-p).bit_length()-1 for p in paths)
            weighted_triple+=Fraction(comb(m+s-1,s),ways[s])
    assert any_triple>=weighted_triple
    return dict(full=any_triple,weighted=str(weighted_triple),denominator=comb(12,6))


def composition_checks():
    checks=0
    for m in range(2,7):
        for N in range(2,6):
            moments={}
            for r in product(range(N+1),repeat=m):
                R=sum(r)
                if R<2:continue
                a=moments.setdefault(R,[0,0])
                a[0]+=1
                a[1]+=sum(comb(x,2) for x in r)
            for R,(num,collisions) in moments.items():
                assert (m+1)*collisions<=2*num*comb(R,2)
                checks+=1
    return checks


def main():
    result=dict(polynomials=[differences(m) for m in range(4,14)],exception=special(),conditional_moment_checks=composition_checks())
    p=Path('/content/archive.zip')
    with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('uniform.json',json.dumps(result))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
