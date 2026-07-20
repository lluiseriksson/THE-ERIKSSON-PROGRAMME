# High-order scaled bridge: frontier narrow unit

**Registered before execution:** 2026-07-20  
**Status:** `DESIGN_ONLY`; no G2/G6 or `(H_tail)` promotion

The paired finite-beta candidate currently ends at
`beta=407/4=101.75`.  The immediately following wider unit hit the frozen
`min_dt` boundary, so this document fixes one narrower, exact successor before
any result is read:

```text
beta unit       [407/4, 3257/32] = [101.75,101.78125]
method          CWIN=3/2 high-order scaled bridge
beta order      30
t order         37
Arb precision   180 bits
min_dt          1/100000
```

The source, tail contract, t-domain, and adaptive subdivision rule are
unchanged.  A valid result requires a fresh production transcript, an
independent replay, exact row equality, and a manifest.  A failure or timeout
retires this unit and does not license unregistered subdivision or inference
of the remainder of `[101.75,1000/9]`.  Even a green pair proves only the
finite-bridge sign predicate on this unit; the sign-to-`(H_tail)` splice and
the other theorem gates remain separate.
