"""Independent rational comparison of the beta integral and the stopped log law."""
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import comb, prod
from pathlib import Path
import hashlib
import json
from zipfile import ZipFile, ZIP_DEFLATED


def integral(row):
    coeff = [F(1)]
    for p in row:
        coeff = [a - p*b for a,b in zip(coeff+[0],[0]+coeff)]
    m = len(row)
    return m*comb(2*m,m)*prod(row)*sum(c/(m+j) for j,c in enumerate(coeff))


def stopped(row):
    m = len(row)
    sums = [F(1)]
    for p in row:
        sums = [p*a + p*(1-p)*b for a,b in zip(sums+[0],[0]+sums)]
    return sum(v*F(comb(m+s-1,s),comb(m,s)) for s,v in enumerate(sums))


def main():
    rows = 0
    strict = 0
    for m in range(2,7):
        for row in combinations_with_replacement([F(i,4) for i in range(5)],m):
            avg = sum(row)/m
            val = integral(row)
            assert val == stopped(row)
            # Rational strengthening from just the product of success probabilities.
            if avg:
                hom = sum(comb(2*m,j)*avg**j*(1-avg)**(2*m-j) for j in range(m,2*m+1))
                assert val*avg**m <= prod(row)*hom
                if len(set(row))>1 and min(row)>0:
                    assert val*avg**m < prod(row)*hom
                    strict += 1
            rows += 1
    packet=Path('/content/archive.zip')
    with ZipFile(packet,'w',ZIP_DEFLATED) as z:
        z.writestr('beta-integral.json',json.dumps(dict(rows=rows,strict=strict)))
    print('archive_sha256',hashlib.sha256(packet.read_bytes()).hexdigest())


if __name__=='__main__':
    main()
