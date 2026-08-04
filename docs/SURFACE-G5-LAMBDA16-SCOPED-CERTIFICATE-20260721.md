# Scoped G5 extension audit: `lambda in [3/2,8/5]`

The previously isolated five-family extension has now been recorded as an
audited scoped candidate.  It covers the five registered delta bands for
`30 <= beta <= 125` and the five adjacent lambda cells

```text
[3/2, 38/25], [38/25, 39/25], [39/25, 79/50],
[79/50, 8/5]
```

with 25 total cells (five width-`1/50` cells indexed 75 through 79).  The production-style validator and the independent
replay validator both pass all 25 rows exactly; the worst outward lower
margin is `0.015093954745680093...` at delta row 3 and lambda cell
`[79/50,8/5]`.  The audit manifest records the two transcript hashes, the
preregistration hash, and the validation scripts.

This audit is deliberately scoped.  It does not modify the G5 gate
row, the finite-beta CWIN=3/2 contract, or G2/G6.  Its immediate use is as an
audited overlap witness for a successor finite-beta bulk contract whose
moving-edge cut is `CWIN=8/5`.
