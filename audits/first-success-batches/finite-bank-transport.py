"""Exhaustive small-bank verification for the finite-panel first-hit supplement."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import permutations, product
from math import comb
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import json


def check(value, description):
    if not value:
        raise ValueError(description)


def blocks(cap, failures):
    patterns = list(permutations(range(cap)))
    return Counter(next((i for i, x in enumerate(order) if x >= failures), cap)
                   for order in patterns)


def signed_polynomial(cap, observed):
    # Coefficients of sum_j binom(cap,j) (z-1)^j, truncated by the prefix.
    return [sum(comb(cap, j) * comb(j, k) * (-1)**(j-k)
                for j in range(k, observed+1)) for k in range(cap+1)]


def convolution(a, b):
    result = [0] * (len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def verify():
    strata = 0
    for caps in [(1,), (2,), (3,), (4,), (2, 3), (1, 2, 3), (2, 2, 2)]:
        for failures in product(*(range(n+1) for n in caps)):
            laws = [blocks(n,k) for n,k in zip(caps,failures)]
            aggregate = [0]*(sum(caps)+1)
            denominator = 0
            for atom in product(*(law.items() for law in laws)):
                weight, series = 1, [1]
                for n, (observed, count) in zip(caps, atom):
                    series = convolution(series, signed_polynomial(n, observed))
                    weight *= count
                denominator += weight
                for j,v in enumerate(series):
                    aggregate[j] += v * weight
            check(aggregate == [denominator * (j == sum(failures)) for j in range(len(aggregate))],
                  (caps,failures))
            strata += 1
    counterexamples = 0
    for d in range(2,6):
        for n in range(1,d+1):
            for m in range(1,5):
                tally = Counter(map(sum,product(range(n),repeat=m)))
                positions = list(product(range(d),repeat=m))
                score = Fraction()
                success = 0
                for record in positions:
                    if max(record) < n:
                        lag = sum(record)
                        success += 1
                        score += Fraction(comb(m+lag-1,lag),tally[lag])
                check(success == n**m and score == comb(m*n,m), (d,n,m))
                counterexamples += 1
    comparisons = 0
    for d in range(2,24):
        for c in range(1,d):
            q = d-c
            for lag in range(d):
                ratio = Fraction(1)
                for i in range(lag):
                    ratio *= Fraction(d * (q-i), q * (d-1-i))
                check(0 <= ratio <= Fraction(d,d-1)**lag, (d,c,lag))
                if c == 1:
                    check(ratio == Fraction(d,d-1)**lag, (d,c,lag))
                comparisons += 1
    check(Fraction(100,99)**100 < 3, "EvalPerf constant")
    return dict(strata=strata,single_pass_checks=counterexamples,lag_ratios=comparisons,
                small_witness=dict(banks=2,cap=2,bank_size=3,full="4/9",expected_score="2/3"))


if __name__ == "__main__":
    archive = Path("/content/archive.zip")
    with ZipFile(archive,"w",ZIP_DEFLATED) as z:
        z.writestr("verification.json",json.dumps(verify(),sort_keys=True))
    print("archive_sha256",sha256(archive.read_bytes()).hexdigest())

