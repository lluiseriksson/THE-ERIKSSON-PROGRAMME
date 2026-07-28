# K2 KD-covariance coefficient series — preregistration

**Registered:** 2026-07-28, before either series grid was executed.

**State:** nominal stress-point design only; no K2, K4, S1/S2, gate, or
manuscript promotion.

The probe integrates, coefficient by coefficient at `t=29/10` and
`delta=0`, the exact covariance identity

```text
Y = 4 * (E[A*G] - E[A]*E[G])
```

under the KD probability weight.  The constant KD cell mass uses the exact
separated Gaussian `erf` integral; all other coefficients use outward-rounded
second-spatial-derivative cell integration.

Frozen parameters:

```text
scaled square = [0,12]^2
grids = 12, then 24
Arb precision = 140 bits
series precision = repository PREC
```

The terminal grid-24 design predicate is:

1. coefficients `Y_0,...,Y_3` are finite;
2. they overlap the four independently derived closed forms
   `T,r2,r3,r4`;
3. the outward radius of `Y_3` is below `1968`, the approximate stress-cell
   ceiling that motivated the normalized endpoint redesign.

Failure rejects this direct coefficientwise second-order spatial integrator.
Pass only licenses a production-grade higher-spatial-order, t-uniform,
companion-and-exterior implementation.  It cannot restore a withdrawn K2
manifest.
