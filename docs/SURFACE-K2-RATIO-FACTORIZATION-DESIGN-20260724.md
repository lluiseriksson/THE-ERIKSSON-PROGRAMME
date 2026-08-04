# K2 ratio-factorization design — preregistration (2026-07-24)

This is a nominal series design brick.  It cannot promote K2, K4, G2, G6, or
the manuscript and it omits the companion/outer-tail terminal charges.

For pointwise factors

```
KD = K d,  KF = K f,  HDD = H d^2,  HDF = H d f,
```

write `r=K/H` and let `r0=r(delta=0)`.  At `delta=0`, `d=2` and `r=r0`,
so the exact pointwise defect

```
g = r - (r0/2) d
```

vanishes.  The production bilinear has the exact algebraic rewrite

```
B = (integral H*d*g)(integral H*d*f)
    - (integral H*f*g)(integral H*d^2).
```

The design probe computes Taylor series around `delta=0`, checks that the
constant coefficient of `g` contains zero, replaces that coefficient by the
algebraically justified exact zero, shifts by one power of `delta`, and
reports nominal enclosures after evaluating the truncated series on
`delta in [0,1/80]`.  This is a conditioning experiment only: truncated
series evaluation is not a rigorous remainder bound.

Acceptance/falsification gates:

1. every spatial cell must report `g0` containing zero;
2. the factorized and direct midpoint bilinears must agree at point tests;
3. any negative/empty enclosure or algebra mismatch stops the design;
4. no output is labelled certified or used to remove a theorem slot.

The preregistered grid-12 run satisfies gates 1--2 algebraically (`g0_bad_cells
=0`), but its nominal `B/delta` radius on `[0,1/80]` is about `3.0e2`--`3.5e2`.
That conditioning is not remotely a terminal margin; the route remains a
design lead and needs centered spatial cells plus the omitted tail charges.
