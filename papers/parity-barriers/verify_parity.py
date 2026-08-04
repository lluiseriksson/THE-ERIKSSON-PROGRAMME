"""Exact rational verification of the parity barrier, r = 1..6.
(a) all character sums of nonempty support, order <= r, vanish on the
    even-parity set (hence all order-<= r marginals are uniform-product);
(b) the last coordinate equals the product of the others on the support,
    with mean 0 and variance 1 under the uniform measure on that support.
Run: python3 verify_parity.py
"""
from fractions import Fraction
from itertools import product, combinations
from math import prod

for r in range(1, 7):
    n = r + 1
    P = [x for x in product([1, -1], repeat=n) if prod(x) == 1]
    N = len(P)
    ok_a = all(
        sum(Fraction(prod(x[i] for i in S)) for x in P) == 0
        for k in range(1, r + 1)
        for S in combinations(range(n), k))
    ok_b = all(x[-1] == prod(x[:-1]) for x in P)
    mean = sum(Fraction(x[-1]) for x in P) / N
    var = sum(Fraction(x[-1] - mean) ** 2 for x in P) / N
    print(f"r={r}: |P|={N}  (a) {ok_a}  (b) {ok_b}  mean={mean}  Var={var}")
    assert ok_a and ok_b and mean == 0 and var == 1
print("ALL EXACT CHECKS PASS")
