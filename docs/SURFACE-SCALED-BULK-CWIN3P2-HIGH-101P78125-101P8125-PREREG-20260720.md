# High-order scaled bridge: frontier continuation

**Registered before execution:** 2026-07-20  
**Status:** `DESIGN_ONLY`; no G2/G6 or `(H_tail)` promotion

The preceding exact unit `[101.75,101.78125]` has a paired candidate
transcript.  This document preregisters the adjacent unit before inspecting
its result:

```text
beta unit       [3257/32, 1629/16] = [101.78125,101.8125]
method          CWIN=3/2 high-order scaled bridge
beta order      30
t order         37
Arb precision   180 bits
min_dt          1/100000
```

All source files, tail conventions, t-domain, and subdivision rules are
unchanged.  Production, independent replay, exact row equality, and a
manifest are required.  A failure or timeout retires this unit; no wider
interval or extrapolation is licensed.  A green pair remains candidate sign
evidence only and does not prove `(H_tail)` or alter G2/G6.
