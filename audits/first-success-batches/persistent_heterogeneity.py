"""Arithmetic checks of the coefficient proof. Run on the programme's own Colab CPU."""
from fractions import Fraction as Q
from hashlib import sha256
from math import comb
from pathlib import Path
import json
from zipfile import ZipFile, ZIP_DEFLATED


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            result[i+j] += u*v
    return result


def profile_checks():
    counts = dict(stationarity=0, profile_values=0, coefficient_bounds=0)
    for n in (2, 3, 5):
        for x in map(Q, ("1/4", "1/2", "1", "3")):
            U = sum(x**j for j in range(n))
            rho = sum(j*x**j for j in range(n))/U
            v = rho/(1+rho)
            c = x/v
            assert c > 1 and (1-v)*sum(j*c**j*v**(j-1) for j in range(1,n)) == U
            counts["stationarity"] += 1
            for q in (Q(i,40) for i in range(41)):
                value = (1-q)*sum((c*q)**j for j in range(n))
                assert (value == (1-v)*U) if q == v else (value < (1-v)*U)
                counts["profile_values"] += 1
            m = rho.denominator
            if m <= 40:
                coefficients = [1]
                for _ in range(m):
                    coefficients = multiply(coefficients, [1]*n)
                s = int(m*rho)
                assert coefficients[s]*x**s*(m*(n-1)+1)**2 >= U**m
                counts["coefficient_bounds"] += 1
    return counts


def masses(probabilities, n):
    full, stopped, ways = [1], [1], [1]
    denom = 1
    for p in probabilities:
        a, d = p.numerator, p.denominator
        b = d-a
        full = multiply(full, [comb(n,k)*a**k*b**(n-k) for k in range(n+1)])
        stopped = multiply(stopped, [a*b**j*d**(n-1-j) for j in range(n)])
        ways = multiply(ways, [1]*n)
        denom *= d**n
    assert sum(full) == denom
    return full, stopped, ways, denom


def audit_pair(pair, m, n=3):
    probabilities = list(map(Q,pair))*(m//2)
    full, stopped, ways, denom = masses(probabilities,n)
    target = sum(full[m:])
    scale = 10**18
    lower = sum(scale*g*comb(m+s-1,m-1)//(w*target)
                for s,(g,w) in enumerate(zip(stopped,ways)))
    upper = lower+len(ways)
    if pair[0] == pair[1]:
        assert lower <= scale <= upper
    return dict(pair=pair,m=m,cap=n,scale=scale,ratio_lower=lower,ratio_upper=upper,
                target_floor=scale*target//denom)


def odds_check():
    ps = [Q(1,10),Q(45,100)]*2
    m = len(ps)
    def values(probs):
        full,g,w,d = masses(probs,3)
        score = sum(Q(y*comb(m+s-1,m-1),w[s]*d) for s,y in enumerate(g))
        return score,Q(sum(full[m:]),d),Q(full[m],d)
    original,target,_ = values(ps)
    tilted,_,atom = values([2*p/(1+p) for p in ps])
    assert original/target <= tilted/atom


if __name__ == "__main__":
    odds_check()
    rows = [audit_pair(pair,m) for pair in (("0.10","0.45"),("0.30","0.85"),("0.49","0.51"),("0.40","0.40"))
            for m in (2,12,48,120,300)]
    report = dict(profiles=profile_checks(),odds_bound_exact=True,rows=rows)
    path = Path("/content/archive.zip")
    with ZipFile(path,"w",ZIP_DEFLATED) as archive:
        archive.writestr("persistent.json",json.dumps(report,indent=2))
    print("archive_sha256",sha256(path.read_bytes()).hexdigest())
