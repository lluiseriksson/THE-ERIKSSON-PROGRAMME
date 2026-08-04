# K2 centered-denominator t-cover — preregistration (2026-07-26)

This campaign tests the centered denominator carrier on the complete sealed
ordered birth partition (indices `0,...,157`) for the first open delta band.
It is a diagnostic cover only and carries no K2, G2, G6, `(H_tail)`, or
manuscript promotion.

Frozen configuration for every row:

```text
delta box: [9/1000,1/100]
center: 19/2000
half-width: 1/2000
spatial grid: 192 x 192
Arb precision: 140 bits
physical split: 1181/1000
```

The row contract computes the nominal moment series about the exact delta
midpoint, subtracts the registered outer-domain constant-term radius, and
charges every higher coefficient over the half-width. Every row must have a
strictly positive outward-rounded uniform `K_D` floor. The campaign ends in
`CENTERED DENOMINATOR COVER PASS` only if all 158 indices occur exactly once;
the first nonpositive row is a terminal carrier failure.

A pass still does not prove the R3 residual, companion/outer-tail budget, or
the S2-direct inequality. Those obligations and independent production/replay
provenance remain mandatory before K2 promotion.
