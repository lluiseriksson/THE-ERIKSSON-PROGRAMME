"""Certified mean scores at several caps on exactly the same task bank."""
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
import hashlib
import json
from zipfile import ZIP_DEFLATED, ZipFile


def capped_coefficients(tasks, cap):
    # Differentiate A=U^tasks, then equate coefficients in U*A'=tasks*U'*A.
    a = [1]
    for s in range(1, tasks*(cap-1)+1):
        total = sum(((tasks+1)*j-s)*a[s-j] for j in range(1,min(cap-1,s)+1))
        v, rem = divmod(total,s)
        assert rem == 0 and v > 0
        a.append(v)
    assert a == a[::-1] and sum(a) == cap**tasks
    return a


def bounds(ell,cap,scale):
    m=ell**3
    h=m//2
    q=Fraction(2,ell)
    a=capped_coefficients(m,cap)
    half=capped_coefficients(h,cap)
    full=1
    numerator=(q.denominator-q.numerator)**h
    denominator=q.denominator**h
    lo=hi=0
    for s,coef in enumerate(half):
        quotient,rem=divmod(scale*numerator*full*coef,denominator*a[s])
        lo+=quotient
        hi+=quotient+bool(rem)
        full=full*(m+s)//(s+1)
        numerator*=q.numerator
        denominator*=q.denominator
    return dict(m=m,cap=cap,lower=lo,upper=hi,scale=scale)


def main():
    for tasks in range(1,6):
        for cap in (2,3,4):
            direct=[0]*(tasks*(cap-1)+1)
            for row in product(range(cap),repeat=tasks):direct[sum(row)]+=1
            assert capped_coefficients(tasks,cap)==direct
    rows=[bounds(ell,n,10**22) for ell in (4,6,8,10,16) for n in (2,3,4)]
    assert all(rows[j]['upper']<rows[j+1]['lower'] for j in range(len(rows)-1) if rows[j]['cap']!=4)
    packet=Path('/content/archive.zip')
    with ZipFile(packet,'w',ZIP_DEFLATED) as z:z.writestr('same-bank.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(packet.read_bytes()).hexdigest())


if __name__=='__main__':
    main()
