"""Verify both finite comparison bounds against independently counted capped compositions."""
from fractions import Fraction as F
from math import comb, log
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib
import json


def coefficients(m, n):
    counts = [1]
    for _ in range(m):
        nxt = [0]*(len(counts)+n-1)
        for s, value in enumerate(counts):
            for j in range(n):
                nxt[s+j] += value
        counts = nxt
    return counts


def compare(m, n, q):
    capped = coefficients(m, n)
    full = [comb(m+s-1, s) for s in range(len(capped))]
    weights = [F(a,b) for a,b in zip(full,capped)]
    assert all(a<=b for a,b in zip(weights,weights[1:]))
    negbin = F(0)
    aux_tail = F(1)
    base = (1-q**n)**m
    joint = (1-q)**m
    for s,w in enumerate(weights):
        negbin += full[s]*joint
        assert negbin <= base*w
        assert base*w*aux_tail <= 1
        aux_tail -= capped[s]*joint/base
        joint *= q
    assert aux_tail == 0
    return len(weights)


def main():
    strata = sum(compare(m,n,q) for m in (2,7,15) for n in range(2,7)
                 for q in (F(1,10),F(1,3),F(4,5)))
    # Half the tasks succeed surely, half have q. The full target is one for n>=2.
    # Compute the two all-hit and score coefficients independently at modest dimensions.
    from decimal import Decimal, localcontext
    rows=[]
    for n in (3,4):
        for m in (32,128,256):
            cap=coefficients(m,n)
            half=coefficients(m//2,n)
            q=F(1,4)
            mean=sum(F(j)*q**j for j in range(n))/sum(q**j for j in range(n))/2
            with localcontext() as ctx:
                ctx.prec=50
                val=sum(Decimal(count)*Decimal(comb(m+s-1,s))/Decimal(cap[s])*Decimal(4)**(-s)
                        for s,count in enumerate(half))*Decimal('0.75')**(m//2)
                rows.append(dict(cap=n,m=m,score=str(val),mu=str(mean)))
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:
        z.writestr('dilute-audit.json',json.dumps(dict(exact_strata=strata,finite_examples=rows)))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())


if __name__=='__main__':
    main()
