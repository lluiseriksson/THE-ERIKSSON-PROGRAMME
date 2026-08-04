#!/usr/bin/env python3
"""Is the reviewer right that my Remark 6.8 sentence is FALSE as written?

I wrote: the 2x2 matrix attains r = tanh(Delta/4), and "by Lemma 6.1 the same is
true along the whole congruence orbit of that matrix."

Lemma 6.1 says Delta is CONSTANT on the orbit.  It does NOT say r is.  If r
moves while Delta stays put, my sentence claims equality at every point of a set
where it holds at one point, and is false.

Measured, not argued.
"""

import math

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
    ev = np.linalg.eigvalsh(T)
    rho = ev.max()
    sub = max(abs(v) for v in ev if not np.isclose(v, rho))
    return sub / rho


def diam(T):
    n = T.shape[0]
    hi = -math.inf
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    hi = max(hi, (T[i, k] * T[j, l]) / (T[j, k] * T[i, l]))
    return math.log(hi)


print("=" * 79)
print("Does r move along the orbit while Delta stays fixed?   M = [[1,mu],[mu,1]]")
print("=" * 79)
print(f"{'mu':>7} {'d1':>8} {'Delta(T)':>11} {'Delta(M)':>11} {'tanh(D/4)':>11} "
      f"{'r(T)':>11} {'r == bound?':>12}")
moved = 0
for mu in (0.1, 0.35, 0.7):
    M = np.array([[1.0, mu], [mu, 1.0]])
    dM, target = diam(M), math.tanh(diam(M) / 4)
    for d1 in (1.0, 0.7, 0.25, 0.05, 0.01):
        D = np.diag([1.0, d1])
        T = D @ M @ D
        dT, rT = diam(T), ratio(T)
        # Delta really is invariant -- that part of my lemma is fine
        check(f"delta-inv mu={mu} d={d1}", abs(dT - dM) < 1e-11,
              f"Delta moved: {dT} vs {dM}")
        # ...and the bound really does hold everywhere -- Birkhoff is fine too
        check(f"bound mu={mu} d={d1}", rT <= target + 1e-11,
              f"r {rT} exceeded tanh(Delta/4) {target}")
        eq = abs(rT - target) < 1e-9
        if not eq:
            moved += 1
        print(f"{mu:>7.2f} {d1:>8.2f} {dT:>11.7f} {dM:>11.7f} {target:>11.8f} "
              f"{rT:>11.8f} {'yes' if eq else 'NO':>12}")
print()
print(f"  points of the orbit where r is STRICTLY BELOW the bound: {moved}")
print("  -> Delta is constant on the orbit, r is not.  The reviewer is right:")
print("     'the same is true along the whole orbit' is FALSE as written.")
print("     What survives is the uniform statement: since Delta is constant and")
print("     ONE point attains the bound, no bound over that orbit depending on")
print("     Delta alone can be smaller.")

print()
print("=" * 79)
print("The surviving statement, checked: sup over the orbit == tanh(Delta/4)")
print("=" * 79)
print(f"{'mu':>7} {'best r found':>14} {'tanh(Delta/4)':>14} {'excess':>12}")
worst = -math.inf
for mu in (0.1, 0.35, 0.7):
    M = np.array([[1.0, mu], [mu, 1.0]])
    target = math.tanh(diam(M) / 4)
    best = max(ratio(np.diag([1.0, d]) @ M @ np.diag([1.0, d]))
               for d in np.linspace(0.01, 1.0, 400))
    check(f"sup mu={mu}", best <= target + 1e-11, f"{best} > {target}")
    check(f"attained mu={mu}", abs(best - target) < 1e-9,
          f"best {best} did not reach {target}")
    worst = max(worst, best - target)
    print(f"{mu:>7.2f} {best:>14.9f} {target:>14.9f} {best-target:>12.2e}")
print(f"  worst excess over the bound: {worst:.2e}  (attained at D = I)")

print()
print("-" * 79)
if BAD:
    print(f"{CHECKS} checks -> {len(BAD)} FAILED")
    for b in BAD[:5]:
        print("   ", b)
    raise SystemExit(1)
print(f"{CHECKS} checks -> ALL PASS")
raise SystemExit(0)
