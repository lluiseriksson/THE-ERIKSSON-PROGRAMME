from math import comb
from itertools import product
from fractions import Fraction as F
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import json,hashlib

def score(m,a,b):
    d=m-2*a-b
    if d<=0:return 1
    return sum((-1)**j*comb(b,j)*2**(b-j) for j in range(d,b+1))

def direct(m):
    # Check at distinct per-batch probabilities by summing stopped records and full trial outcomes.
    probs=[F(i+1,m+2) for i in range(m)]
    total=F(0)
    for record in product(range(3),repeat=m):
        p=F(1);a=record.count(1);b=record.count(2)
        for x,z in zip(record,probs):p*=((1-z)**2,z,z*(1-z))[x]
        total+=p*score(m,a,b)
    distribution=[F(1)]
    for z in probs:
        for _ in range(2):
            v=[F(0)]*(len(distribution)+1)
            for j,h in enumerate(distribution):v[j]+=(1-z)*h;v[j+1]+=z*h
            distribution=v
    assert total==sum(distribution[m:])

def main():
    result={}
    for m in range(1,81):
        values=[(score(m,a,b),a,b) for a in range(m+1) for b in range(m-a+1)]
        lo=min(values);hi=max(values)
        if m<=7:direct(m)
        for y,a,b in values:
            d=m-2*a-b
            if 1<=d<=b:
                assert 0<(-1)**d*y<=comb(b,d)*2**(b-d)
        if m in [2,3,4,8,16,32,64,80]:
            result[m]=dict(minimum=lo,maximum=hi)
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('signed.json',json.dumps(result,indent=2))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
