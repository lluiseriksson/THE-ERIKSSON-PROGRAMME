# K2 centred spatial ratio-factorization design — preregistration (2026-07-24)

This is a conditioning experiment only.  It carries no K2, G2, G6, K4, or
manuscript promotion and omits the companion and outer-tail charges.

The exact product-of-sums identity is evaluated after extracting
`g=r-(r0/2)d`, where `r=K/H` and `d=dw`.  The four spatially integrated series
are

```
Gd = integral H*d*(g/delta),  Df = integral H*d*f,
Gf = integral H*f*(g/delta),  Dd = integral H*d^2.
```

The bilinear quotient numerator is `Gd*Df-Gf*Dd`.  Each factor is integrated
cell-by-cell with the existing midpoint plus Hessian remainder rule, so the
spatial dependence is not multiplied across unrelated wide boxes before the
exact `g(0)=0` shift.

Frozen smoke configuration:

```
delta lane: [0,1/80], t: 2.90 and 3.13, spatial side: 12,
grids: 12 and 24, Arb precision: 140 bits, Taylor order: 6.
```

Acceptance/falsification: all cell values and all five spatial dual
components of `g` at delta zero must contain zero; otherwise the route is
rejected.  The output is nominal truncated-series evidence only and cannot
be used as a terminal margin.
