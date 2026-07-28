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
