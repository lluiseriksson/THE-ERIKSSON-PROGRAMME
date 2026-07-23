# High-order `CWIN=3/2` continuation unit: `[79.75,79.875]`

**Registered:** 2026-07-23, before production

This unit uses the unchanged high-order contract: beta order 30, t order 37,
180 Arb bits, `min_dt=1/100000`, and `CWIN=3/2`. The exact beta box is
`[319/4,1278/16]`; the t cover must run from `3/5` to the conservative moving
edge `pi-(3/2)/beta_hi`. Production and independent replay must be
byte-identical and pass the existing structural validator. The result is
candidate sign evidence only and carries no `(H_tail)`, G2, or G6 promotion.
