# K2 shift-centered fixed-square complex supremum — preregistration

**Registered:** 2026-07-28, after the uncentered grid-48 failure and before
any centered arc was evaluated.

**State:** nominal stress-cell design only; no K2, K4, S1/S2, gate, or
manuscript promotion.

For each theta arc, choose point complex constants `a0,g0` from the midpoint
of the outward-rounded global means.  Covariance is exactly shift-invariant:

```text
Cov(A,G)=Cov(A-a0,G-g0).
```

The centered integrands are evaluated directly on each spatial interval cell;
they are not reconstructed by subtracting four already-summed global
moments.  All circle, companion, series-tail, Cauchy-budget, and precision
parameters remain those frozen in
`SURFACE-K2-FIXED-SQUARE-COMPLEX-SUPREMUM-PREREG-20260728.md`.

The frozen refinement ladder is

```text
(spatial grid, theta arcs) = (24,32), (48,64), (96,128).
```

The first level with strict complex KD modulus and
`M_sup<M_required=0.654...` passes the design.  Exhaustion fails it.  Even a
pass remains fixed-square nominal evidence: true companions, the real moving
exterior, and the global t-cover stay open.

## Result

The complete frozen ladder was exhausted.  At the terminal `96 x 128` level,
the complex denominator remained strictly resolved,

```text
|KD| >= 2.3351532779633998,
```

and exact shift-centering reduced the worst circle enclosure from the
uncentered `30.3687` to

```text
M_sup <= 2.2118834741413594.
```

This still exceeds the preregistered degree-five requirement
`M_required=0.654168`, so the terminal verdict is

```text
K2 FIXED-SQUARE CENTERED COMPLEX SUPREMUM DESIGN FAIL;
EXTERIOR AND TRUE COMPANION OPEN
```

The failure retires further blind spatial refinement at companion degree
five.  It is nevertheless a quantitative design result: the centered
surrogate is within a factor `3.39` of the old threshold.  Any later use of
new exact heads must preregister a new companion degree and Cauchy exponent;
this transcript cannot be relabelled as that later certificate.

Transcript SHA-256:

```text
raw CRLF 5145ACFA8D11766F982555B2350102F84E0108CA6CE1ED69D4443DFF38F078CE
LF       B93BC47653F30B23298002700EE354996C847175CFBBBB9134250683CC422B29
```
