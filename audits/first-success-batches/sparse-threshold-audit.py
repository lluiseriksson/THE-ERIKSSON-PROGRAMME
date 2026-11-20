"""Finite audit of an improving bank at the pooled threshold. Python standard library."""
from fractions import Fraction
from math import comb
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib
import json


def capped_recurrence(count, cap):
    # Compare coefficients in U C' = count U' C, where C=U**count.
    coeff = [1]
    for k in range(1, count*(cap-1)+1):
        raw = sum(((count+1)*j-k)*coeff[k-j] for j in range(1,min(cap-1,k)+1))
        value, rem = divmod(raw,k)
        assert rem == 0 and value > 0
        coeff.append(value)
    assert sum(coeff) == cap**count and coeff == coeff[::-1]
    return coeff


def audit(m, r, cap, p, digits=260):
    rest = m-r
    total = cap*rest
    b, den = p.numerator, p.denominator
    miss = den-b
    cut = max(0,m-cap*r)
    tail = sum(comb(total,i)*b**i*miss**(total-i) for i in range(cut,total+1))
    assert 0 < tail <= den**total
    unrestricted = capped_recurrence(rest,cap)
    allowed = capped_recurrence(m,cap)
    scale = 10**digits
    low = high = 0
    for s,c in enumerate(unrestricted):
        mass = c*b**rest*miss**s*den**(total-rest-s)
        numerator = mass*comb(m+s-1,s)
        quotient, rem = divmod(numerator*scale,allowed[s]*tail)
        low += quotient
        high += quotient + bool(rem)
    assert 0 < low <= high and high-low <= len(unrestricted)
    return dict(m=m,r=r,p=str(p),cap=cap,ratio_bounds=[str(low),str(high)],
                denominator_power_of_ten=digits,
                full_target_bounds_at_1e12=[tail*10**12//den**total,-((-tail*10**12)//den**total)])


def direct(m,r,cap,p):
    # Forward dynamic programs over actual attempts and the stopped wait log.
    probs = [Fraction(1)]*r+[p]*(m-r)
    total = [Fraction(1)]
    logs = [Fraction(1)]
    counts = [1]
    for prob in probs:
        for _ in range(cap):
            nxt = [Fraction(0)]*(len(total)+1)
            for i,v in enumerate(total):
                nxt[i] += v*(1-prob)
                nxt[i+1] += v*prob
            total = nxt
        nxt = [Fraction(0)]*(len(logs)+cap-1)
        ways = [0]*len(nxt)
        for s,v in enumerate(logs):
            for j in range(cap):
                nxt[s+j] += v*prob*(1-prob)**j
                ways[s+j] += counts[s]
        logs, counts = nxt, ways
    target = sum(total[m:])
    return sum(v*Fraction(comb(m+s-1,s),counts[s]) for s,v in enumerate(logs))/target


def main():
    rows = []
    checks = 0
    for cap in (2,3):
        for m in (3,5,8,16):
            for r in (1,m//2):
                for p in (Fraction(1,cap),Fraction(1,2*cap)):
                    row = audit(m,r,cap,p)
                    lower,upper = map(int,row['ratio_bounds'])
                    exact = direct(m,r,cap,p)
                    assert lower <= exact*10**260 <= upper
                    checks += 1
    for base in (4,6,8):
        for p in (Fraction(1,3),Fraction(1,6)):
            rows.append(audit(base**3,base**2,3,p))
    archive = Path('/content/archive.zip')
    with ZipFile(archive,'w',ZIP_DEFLATED) as z:
        z.writestr('sparse-threshold.json',json.dumps(dict(small_checks=checks,rows=rows)))
    print('archive_sha256',hashlib.sha256(archive.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
