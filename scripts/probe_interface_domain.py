#!/usr/bin/env python3
"""Is the reviewer's counterexample to `SpectralInterface` real?

The Lean hypothesis I published quantifies over EVERY entrywise positive T, with
no symmetry.  The reviewer claims that for

    T = [[3,5,2],[5,4,1],[2,5,3]]

(positive, all row sums 10, eigenvalues 10, 1, -1, so r(T) = 0.1) the premises
hold with b = 1.3 and a = 10 while the conclusion b/a = 0.13 <= r(T) = 0.1 is
false.  The mechanism: x^T T x = x^T S x with S = (T+T^t)/2, and Courant-Fischer
on S gives, for EVERY Omega, some x perp Omega with x^T S x >= lambda_2(S).

If that is right then my hypothesis is not "two textbook facts packaged".  It is
FALSE for the intended r -- and a conditional theorem whose hypotheses no real r
satisfies is vacuous, which is a worse failure than an over-strong domain.

Also checks that ADDING symmetry repairs it, which is the proposed fix.
"""

import numpy as np

CHECKS = 0
BAD = []


def check(name, cond, detail=""):
    global CHECKS
    CHECKS += 1
    if not cond:
        BAD.append(f"{name}: {detail}")
    return bool(cond)


def ratio(T):
    ev = np.linalg.eigvals(T)
    rho = max(ev.real)
    sub = max(abs(v) for v in ev if not np.isclose(v.real, rho) or abs(v.imag) > 1e-9)
    return sub / rho, ev


T = np.array([[3.0, 5.0, 2.0],
              [5.0, 4.0, 1.0],
              [2.0, 5.0, 3.0]])

print("=" * 79)
print("THE COUNTEREXAMPLE")
print("=" * 79)
print("T =", T.tolist())
print("entries all positive :", bool((T > 0).all()))
print("row sums            :", T.sum(axis=1).tolist())
ev = np.linalg.eigvals(T)
ev_sorted = sorted(ev, key=lambda z: -z.real)
print("eigenvalues         :", [complex(round(v.real, 10), round(v.imag, 10)) for v in ev_sorted])
rho = max(v.real for v in ev)
sub = max(abs(v) for v in ev if not np.isclose(v.real, rho))
rT = sub / rho
print(f"rho = {rho:.10f}   subdominant modulus = {sub:.10f}   r(T) = {rT:.10f}")

S = (T + T.T) / 2
evS = np.sort(np.linalg.eigvalsh(S))[::-1]
print("symmetric part S    =", S.tolist())
print(f"eigenvalues of S    : {evS[0]:.6f}, {evS[1]:.6f}, {evS[2]:.6f}")
lam2 = evS[1]

check("entries positive", bool((T > 0).all()))
check("row sums = 10", np.allclose(T.sum(axis=1), 10.0))
check("r(T) = 0.1", abs(rT - 0.1) < 1e-9, f"r = {rT}")
check("lambda2(S) > 1.3", lam2 > 1.3, f"lambda2 = {lam2}")

print()
print("=" * 79)
print("PREMISE: for EVERY positive Omega, is there x perp Omega with x'Tx >= b|x|^2 ?")
print("=" * 79)
b, a = 1.3, 10.0
rng = np.random.default_rng(20260802)
worst = np.inf
for trial in range(4000):
    Om = rng.uniform(0.01, 5.0, 3)
    # best Rayleigh quotient of T over the plane orthogonal to Omega
    Q, _ = np.linalg.qr(np.column_stack([Om, rng.normal(size=3), rng.normal(size=3)]))
    B = Q[:, 1:]                     # orthonormal basis of Omega^perp
    best = np.linalg.eigvalsh(B.T @ S @ B).max()   # x'Tx = x'Sx
    worst = min(worst, best)
    check(f"premise trial {trial}", best >= b - 1e-9,
          f"best Rayleigh {best} < b {b}")
print(f"  over 4000 random positive Omega, the WORST attainable value was {worst:.9f}")
print(f"  premise threshold b = {b}  ->  premise holds: {worst >= b}")
print(f"  (Courant-Fischer floor is lambda2(S) = {lam2:.9f})")

print()
print("=" * 79)
print("VERDICT on the published hypothesis")
print("=" * 79)
concl = b / a
print(f"  premises satisfied with b = {b}, a = {a} (all row sums <= a)")
print(f"  conclusion demanded : b/a = {concl:.6f} <= r(T) = {rT:.6f}")
print(f"  -> {'FALSE, the reviewer is right' if concl > rT else 'holds'}")
check("interface is refuted", concl > rT,
      f"expected {concl} > {rT}")

print()
print("=" * 79)
print("DOES ADDING SYMMETRY REPAIR IT?  (the proposed fix)")
print("=" * 79)
print("With T symmetric, x'Tx IS the quadratic form of T itself, Perron-Frobenius")
print("gives a positive top eigenvector Omega1, and Courant-Fischer at Omega=Omega1")
print("makes the premise's best value exactly lambda2(T).  Checked on random")
print("symmetric positive matrices:")
print(f"{'n':>3} {'b=lam2':>12} {'rho':>12} {'row bd a':>12} {'b/a':>12} {'r(T)':>12}  ok")
for n in (3, 4, 6):
    for t in range(60):
        A = rng.uniform(0.05, 1.0, (n, n))
        A = (A + A.T) / 2
        e = np.linalg.eigvalsh(A)
        rho_s, lam2_s = e[-1], e[-2]
        aa = A.sum(axis=1).max()
        rr = max(abs(v) for v in e if not np.isclose(v, rho_s)) / rho_s
        ok = (lam2_s / aa) <= rr + 1e-12
        check(f"sym n={n} t={t}", ok, f"{lam2_s/aa} > {rr}")
        if t == 0:
            print(f"{n:>3} {lam2_s:>12.6f} {rho_s:>12.6f} {aa:>12.6f} "
                  f"{lam2_s/aa:>12.6f} {rr:>12.6f}  {'ok' if ok else 'FAIL'}")

print()
print("-" * 79)
if BAD:
    print(f"{CHECKS} checks -> {len(BAD)} FAILED")
    for x in BAD[:5]:
        print("   ", x)
    raise SystemExit(1)
print(f"{CHECKS} checks -> ALL PASS "
      "(the counterexample is real; symmetry repairs the interface)")
raise SystemExit(0)
