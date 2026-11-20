from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb, prod
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib, json

def coefficients(m,n):
    waits=list(product(range(n),repeat=m))
    counts=Counter(sum(u) for u in waits)
    # Enumerate true success counts then expand q^(n-k)(1-q)^k.
    d=Counter()
    for k in product(range(n+1),repeat=m):
        if sum(k)<m: continue
        mass=prod(comb(n,v) for v in k)
        for j in product(*(range(v+1) for v in k)):
            powers=tuple(n-h+v for h,v in zip(k,j))
            d[powers]+=(-1)**sum(j)*mass*prod(comb(h,v) for h,v in zip(k,j))
    for u in waits:
        s=sum(u); weight=F(comb(m+s-1,m-1),counts[s])
        for mask in product((0,1),repeat=m):
            powers=tuple(v+a for v,a in zip(u,mask))
            d[powers]-=weight*(-1)**sum(mask)
    return {k:v for k,v in d.items() if v},counts[n]

def audit(m,n):
    d,a=coefficients(m,n); t=m*n
    assert a==comb(m+n-1,m-1)-m
    actual={k:v for k,v in d.items() if sum(k)<=n}
    expected={k:(1 if max(k)==n else -F(m,a)) for k in product(range(n+1),repeat=m) if sum(k)==n}
    assert actual==expected
    # Diagonal jet, computed coefficient by coefficient at every total degree.
    for deg in range(t+1):
        items=[(k,v) for k,v in d.items() if sum(k)==deg]
        assert sum(v for k,v in items)==0
        assert all(sum(k[i]*v for k,v in items)==0 for i in range(m))
    b=3**t+2**m*comb(t,m); norm=sum(abs(v) for v in d.values());assert norm<=b
    eps=F(m,2*a*t*(t-1)*b)
    return dict(batches=m,cap=n,nonzero_terms=len(d),first_degree=n,norm=str(norm),bound=b,epsilon=str(eps))

def main():
    rows=[audit(m,n) for m,n in ((2,2),(2,5),(3,2),(3,3),(3,4),(4,3))]
    out=Path('/content/archive.zip')
    with ZipFile(out,'w',ZIP_DEFLATED) as z:z.writestr('high-reliability.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(out.read_bytes()).hexdigest())
if __name__=='__main__':main()
