from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb,prod
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json

def check(m,n):
    T=m*n; C=comb(T,m); h=comb(n,2)*n**(m-2)
    ways=Counter(sum(u) for u in product(range(n),repeat=m))
    assert sum(comb(m+s-1,m-1) for s in ways)==C
    samples=0
    for numerators in product((1,3,8),repeat=m):
        p=tuple(F(v,9) for v in numerators); M=C*prod(p); S=0; target=0
        for ks in product(range(n+1),repeat=m):
            if sum(ks)<m:continue
            probterm=prod(comb(n,k)*a**k for a,k in zip(p,ks))
            if sum(ks)==m:S+=probterm
            target+=probterm*prod((1-a)**(n-k) for a,k in zip(p,ks))
        correction=sum((p[i]-p[j])**2/(p[i]*p[j]) for i in range(m) for j in range(i))
        lower=M*(1+F(h,C)*correction)
        assert S>=lower
        score=prod(p)*sum(F(comb(m+sum(u)-1,m-1),ways[sum(u)])*prod((1-a)**v for a,v in zip(p,u)) for u in product(range(n),repeat=m))
        assert score<=M and target>=(1-max(p))**(T-m)*S
        if lower*(1-max(p))**(T-m)>M: assert target>score
        samples+=1
    return dict(batches=m,cap=n,samples=samples)

def main():
    rows=[check(m,n) for m,n in ((2,2),(2,4),(3,2),(3,3),(4,2))]
    out=Path('/content/archive.zip')
    with ZipFile(out,'w',ZIP_DEFLATED) as z:z.writestr('rare.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(out.read_bytes()).hexdigest())
if __name__=='__main__':main()
