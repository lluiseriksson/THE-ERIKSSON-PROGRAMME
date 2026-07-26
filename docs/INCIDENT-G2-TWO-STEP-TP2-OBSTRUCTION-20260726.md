# Incident — two-step midpoint TP2 route falsified (2026-07-26)

## Candidate tested

The four-step bridge midpoint kernel is

```text
k_beta(u,v) = 4 sum_{m>=1} I_m(beta)^2 sin(m u) sin(m v).
```

If this kernel were TP2, the positive bridge weight would have supplied a
direct stochastic-order proof of `E'(t)<0`, avoiding the unresolved bulk
Wronskian.  The fact that the one-step killed von Mises kernel is not TP2 did
not logically rule out this two-step possibility, so it was tested separately.

## Certified counterexample

`scripts/certify_two_step_midpoint_not_tp2.py` uses 220-bit Arb arithmetic,
scaled Bessel values, and a geometric positive tail bound.  At
`beta=10`,

```text
u1=36*pi/40 < u2=37*pi/40,
v1=2*pi/40 < v2=3*pi/40,
```

the determinant `k(u1,v1)k(u2,v2)-k(u1,v2)k(u2,v1)` has a strictly negative
outward-rounded upper endpoint.  The script is an executable certificate of
the obstruction, not a numerical point estimate.

## Disposition

The midpoint-TP2/MLR shortcut is rejected.  This does not disprove the
Surface Theorem; it only removes a structurally attractive route to G2.
