from math import comb,prod
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import json,hashlib


def ways(n,m,s):
    return sum((-1)**j*comb(m,j)*comb(s-n*j+m-1,m-1) for j in range(min(s//n,m)+1))


def weight(n,m,s):
    return F(comb(s+m-1,m-1),ways(n,m,s))


def envelope(n):
    f=n+3
    B=comb(n+2,2)-9
    den=[ways(n,4,f-e) for e in range(4)]
    upper=B*sum(comb(2*n-4+e,e)*(weight(n,4,f-e)-1) for e in range(4))
    val=(6*n*comb(n,2)-upper)*prod(den)
    assert val.denominator==1
    return val.numerator


def exact_small(n,m):
    f=n+3
    full=6*n*comb(n,2)
    dem=F(0)
    for a in product(range(1,n),repeat=3):
        if sum(a)!=f:continue
        for late in product(range(4),repeat=3):
            e=sum(late)
            if e>3 or any(t>y for t,y in zip(late,a)):continue
            mult=prod(comb(n-y+t-1,t) for y,t in zip(a,late))
            dem+=mult*(weight(n,m,f-e)-1)
    return dict(n=n,m=m,demand=str(dem),supply=full,passes=dem<=full)


def main():
    # n>=4 gives s<=n+3<2n. Each of four denominators has degree 3.
    # The cleared supply term has degree <=15; cleared demand degree <=14.
    for origin in range(4,31):
        row=[envelope(n) for n in range(origin,origin+17)]
        coeff=[]
        while row:
            coeff.append(row[0]);row=[b-a for a,b in zip(row,row[1:])]
        assert coeff[-1]==0
        if min(coeff)>=0:break
    else:raise ValueError('Newton envelope could not be certified')
    for n in [origin,30,120]:assert sum(v*comb(n-origin,i) for i,v in enumerate(coeff))==envelope(n)
    small=[exact_small(n,m) for n in range(3,origin) for m in (4,5,6,7,8)]
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('three-failures.json',json.dumps(dict(origin=origin,coefficients=coeff,small=small)))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
