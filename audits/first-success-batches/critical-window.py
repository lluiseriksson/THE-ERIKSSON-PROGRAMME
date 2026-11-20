"""Exact composition counts and finite means for the two-class transition example."""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import hashlib
import json
from zipfile import ZipFile, ZIP_DEFLATED


def capped(m, s, n):
    return sum((-1)**j * comb(m, j) * comb(m + s - n*j - 1, m - 1)
               for j in range(min(m, s//n) + 1))


def main():
    enumerated = 0
    for m in range(2, 6):
        for n in range(2, 5):
            counts = [0] * (m*(n-1)+1)
            for row in product(range(n), repeat=m):
                counts[sum(row)] += 1
            for s, count in enumerate(counts):
                assert capped(m, s, n) == count
                enumerated += 1
    # Cap two, half the tasks certain, half failing with probability 2/l.
    # On all-hit records the unconditioned weight at total wait s is
    # (1-q)^h * binom(h,s) q^s, h=m/2. P=1 identically.
    rows = []
    for ell in (4, 8, 16, 32, 48):
        m = ell**2
        h, q = m//2, F(2, ell)
        term = (1-q)**h
        total = term
        for s in range(h):
            term *= q*(h-s)*(m+s)/((s+1)*(m-s))
            total += term
        if ell <= 8:
            direct = sum((1-q)**h * comb(h,s)*q**s * F(comb(m+s-1,s),capped(m,s,2))
                         for s in range(h+1))
            assert direct == total
        lo = total.numerator * 10**10 // total.denominator
        rows.append(dict(m=m, lower_1e10=lo, upper_1e10=lo+1))
    packet = Path('/content/archive.zip')
    with ZipFile(packet,'w',ZIP_DEFLATED) as z:
        z.writestr('critical-window.json',json.dumps(dict(cells=enumerated, rows=rows)))
    print('archive_sha256',hashlib.sha256(packet.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
