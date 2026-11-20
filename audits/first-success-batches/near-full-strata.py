from math import comb
from fractions import Fraction as F
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json


def weight(n,m,s):
    ways=sum((-1)**j*comb(m,j)*comb(m+s-j*n-1,m-1) for j in range(min(m,s//n)+1))
    return F(comb(m+s-1,m-1),ways)


def two_slot(n,m):
    # a,b failures on two all-hit tasks, with e late failures among those tasks.
    supply=2*comb(n,2)
    extra=F(0)
    for a in range(3,n):
        b=n+2-a
        for e in range(3):
            multiplicity=sum(comb(n-a+j-1,j)*comb(n-b+e-j-1,e-j) for j in range(e+1))
            extra+=multiplicity*(weight(n,m,n+2-e)-1)
    if n>=4 and m==2: assert extra==supply
    assert 0<=extra<=supply
    return str(extra)

def main():
    tests=[(n,m,two_slot(n,m)) for n in list(range(3,16))+[20,32] for m in (2,3,4,6,12,30,100)]
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('upper.json',json.dumps(dict(checked=len(tests),pairs=tests)))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
