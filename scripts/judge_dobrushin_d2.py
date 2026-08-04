#!/usr/bin/env python3
"""Pre-registered gate for D-2a of the Dobrushin lane.

WRITTEN AND COMMITTED BEFORE ANY COMPUTATION OF THE QUANTITY IT JUDGES, and it
predicts an IDENTITY rather than a range.  No threshold in this file was chosen
after seeing a number.

THE PREDICTION.  For a two-state site in local field `h`, the conditional is
`p(s) ∝ exp(h·s)`, so `P(+1) = (1 + tanh h)/2`.  Flipping one neighbour across a
bond of strength `J` moves the field from `h` to `h - 2J`.  The total-variation
distance between the two conditionals is `|P_h(+1) − P_{h−2J}(+1)|`.  D-2a
claims that its supremum over `h` is EXACTLY

        sup_h |P_h(+1) − P_{h−2J}(+1)|  =  tanh|J|,

attained at `h = J` (where the two fields are `+J` and `−J`).  That number,
summed over the neighbours of a site, is the Dobrushin coefficient, and it is
what makes the window of this lane `2 tanh β + 2 tanh γ < 1`.

  J5  the supremum equals tanh|J| to 1e-12, on pre-registered J
  J6  it is ATTAINED at h = J, to 1e-12 --- a supremum that is not attained
      would leave the constant unproved even if the bound held
  J7  the bound is never violated on a dense sweep of h --- a single violation
      refutes D-2a outright

Exits non-zero on failure.  No `assert` anywhere: `python -O` deletes those, and
this repository has already had two certifiers emit a false PASS that way.  PASS
is printed only after an explicit counter confirms every check actually ran.

ENVIRONMENT: prepared on the desktop with the runtime disconnected; RUN ON
COLAB.  No reliable measurement of its cost exists, so the owner's rule of
2026-08-01 presumes it heavy.
"""

import sys
import math

FAILURES = []
CHECKS = 0
EXPECTED_CHECKS = 18          # 6 J-values x (J5 + J6 + J7)

# pre-registered, spanning weak to strong bonds and both signs
J_VALUES = [0.05, 0.2, 0.5, 1.0, 2.0, -0.7]
TOL = 1e-12
SWEEP = 200001                # h from -20 to 20
H_LO, H_HI = -20.0, 20.0


def check(ok, gate, msg):
    global CHECKS
    CHECKS += 1
    if not ok:
        FAILURES.append(f"{gate}: {msg}")
        print(f"    FAIL  {msg}")
    return ok


def p_plus(h):
    """P(+1) for a two-state site in field h, written from the Boltzmann
    weights and from nothing else."""
    return (1.0 + math.tanh(h)) / 2.0


def tv(h, J):
    return abs(p_plus(h) - p_plus(h - 2.0 * J))


def main():
    print("=" * 74)
    print("GATE D-2a — the single-site Dobrushin coefficient of an Ising bond")
    print("prediction, registered before computation:  sup_h TV = tanh|J|,")
    print("attained at h = J.  Not a range: an identity.")
    print("=" * 74)
    print(f"{'J':>6} {'predicted':>14} {'sup over sweep':>16} {'at h=J':>14}"
          f" {'max violation':>15}")
    print("-" * 70)

    step = (H_HI - H_LO) / (SWEEP - 1)
    for J in J_VALUES:
        predicted = math.tanh(abs(J))
        best, worst_viol = 0.0, 0.0
        for i in range(SWEEP):
            h = H_LO + i * step
            v = tv(h, J)
            if v > best:
                best = v
            if v - predicted > worst_viol:
                worst_viol = v - predicted
        at_J = tv(J, J)

        # J5 --- the supremum is the predicted identity.  The sweep can only
        # approach it, so compare the ATTAINED value, which is exact.
        check(abs(at_J - predicted) <= TOL, "J5",
              f"J={J}: sup differs from tanh|J| by {abs(at_J - predicted):.3e}")
        # J6 --- and it is attained at h = J, i.e. the sweep never beats it
        check(best <= at_J + TOL, "J6",
              f"J={J}: sweep found {best:.15f} above the claimed attained "
              f"value {at_J:.15f}")
        # J7 --- the bound is never violated
        check(worst_viol <= TOL, "J7",
              f"J={J}: bound violated by {worst_viol:.3e}")

        print(f"{J:6.2f} {predicted:14.12f} {best:16.12f} {at_J:14.12f}"
              f" {worst_viol:15.3e}")

    print()
    print(f"checks performed: {CHECKS} (expected {EXPECTED_CHECKS})")
    if CHECKS < EXPECTED_CHECKS:
        print(f"VERDICT: FAIL — only {CHECKS} checks ran; an empty failure list "
              f"is not a verdict when the gates did not execute")
        return 1
    if FAILURES:
        print(f"VERDICT: FAIL ({len(FAILURES)})")
        for f in FAILURES:
            print("  -", f)
        return 1
    print("VERDICT: PASS — sup_h TV = tanh|J|, attained, never exceeded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
