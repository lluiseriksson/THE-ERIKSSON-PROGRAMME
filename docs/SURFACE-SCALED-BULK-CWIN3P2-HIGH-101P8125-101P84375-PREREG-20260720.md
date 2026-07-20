# High-order scaled bridge: frontier continuation II

**Registered before execution:** 2026-07-20  
**Status:** `DESIGN_ONLY`; no G2/G6 or `(H_tail)` promotion

The paired candidate currently reaches `beta=1629/16=101.8125`.  This exact
adjacent unit is frozen before execution:

```text
beta unit       [1629/16, 3259/32] = [101.8125,101.84375]
method          CWIN=3/2 high-order scaled bridge
beta order      30
t order         37
Arb precision   180 bits
min_dt          1/100000
```

No source, tail, t-domain, or subdivision rule changes.  Production and an
independent replay with exact row equality are required.  Failure or timeout
retires this unit; no wider interval or extrapolation is admitted.  A green
pair remains candidate sign evidence only and does not prove `(H_tail)` or
alter G2/G6.
