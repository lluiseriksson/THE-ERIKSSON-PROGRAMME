# Incident: order-22 repair reaches the minimum t width at unit 57

**Date:** 2026-07-22

The preregistered order-22 repair contract was run on unit 57,
`[125/2,251/4]`, with `CWIN=3/2`, beta order 22, t order 25, 180-bit Arb,
and minimum width `1/100000`.  The recursive cover reached that floor near
`t=3.114269215658235` and raised:

```text
RuntimeError: order22 repair cover failure near t=3.114269215658235
```

The driver emitted no terminal transcript, so unit 57 carries no sign-row,
G2, G6, or `H_tail` load.  Units 32--56 remain the admitted quarantined
repair evidence.  Any higher-order attempt must be preregistered separately,
retain the same mesh and stopping rule, and pass fresh production/replay
validation before it can be archived.

That separate repair is preregistered at
`docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER24-REPAIR-EXTENSION-PREREG-20260722.md`.
Order 24 passes units 57--59 with 635 rows in fresh production and replay,
byte-for-byte; the result is archived as quarantined evidence in
`run-manifests/surface-scaled-bulk-cwin3p2-mid-cover-order24-repair-unit57-20260722.json`.
It remains sign evidence only and carries no relay or theorem load.
