# Preregistration: CWIN=3/2 pilot in the gap `[31,74]`

**Date:** 2026-07-22  
**Scope:** candidate pilot only; no G2/G6 promotion.

This pilot tests the frozen high-order CWIN=3/2 contract at three adversarial
locations in the current relay gap:

```text
gap31_31p0625       beta [31,497/16]
gap52_52p0625       beta [52,833/16]
gap73p9375_74       beta [1183/16,74]
```

Each cell uses `run_surface_scaled_bulk_cwin3p2_high_unit.py` with
`CWIN=3/2`, beta order 30, t-order 37, minimum t width `1/100000`, and 180
Arb bits.  Production and a fresh replay are required.  Acceptance requires
finite strictly negative outward-rounded upper endpoints on an adjacent
terminal t-row cover from `3/5` through
`pi - (3/2)/beta_lo`, plus matching dependency hashes and the candidate-only
footer.

The decision rule is fixed before reading results: a failure at width `1/16`
is a terminal incident for that pilot cell; no adaptive rescue or relabelling
is permitted.  Passing cells remain candidate evidence and do not establish
`(H_tail)`, the finite-beta relay, G2, or G6.  The exact scaling/sign relay
logic and its domain conditions are recorded separately in
`SURFACE-FINITE-W-SIGN-RELAY-LOGICAL-AUDIT-20260722.md`.
