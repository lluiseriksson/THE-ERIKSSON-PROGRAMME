"""Exact finite-difference certificate for all integer caps in the k=m+2 layer."""
from math import comb,factorial
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import json,hashlib


def envelope(m,n):
    k=m+2
    no_triple=sum(comb(m,j)*comb(m-j,k-2*j)*comb(n,2)**j*n**(k-2*j)
                  for j in range(2,k//2+1))
    return 2*(comb(m*n,k)-no_triple)-(n-2)*comb(m*n,k-1)


def certify(m):
    # Left side is polynomial in n of degree at most m+2.
    level=[envelope(m,n) for n in range(3,3+m+4)]
    coeff=[]
    while level:
        coeff.append(level[0])
        level=[b-a for a,b in zip(level,level[1:])]
    assert coeff[-1]==0
    coeff.pop()
    for n in (3,4,12,100,1000):
        assert sum(c*comb(n-3,i) for i,c in enumerate(coeff))==envelope(m,n)
    return dict(m=m,certified=all(c>=0 for c in coeff),differences=coeff)


def main():
    rows=[certify(m) for m in range(2,85)]
    path=Path('/content/archive.zip')
    with ZipFile(path,'w',ZIP_DEFLATED) as z:
        z.writestr('two-extra.json',json.dumps(rows,separators=(',',':')))
    print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=='__main__':main()
