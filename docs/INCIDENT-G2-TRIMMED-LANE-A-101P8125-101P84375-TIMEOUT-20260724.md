# Two-lane G2 splice: Lane-A timeout

**Status:** `DESIGN_TIMEOUT`, no G2/G6 promotion

Under the pre-registered two-lane collar contract in
`SURFACE-G2-TWO-LANE-COLLAR-PREREG-20260724.md`, Lane A was run with
`CWIN=19/10`, order 40, t-order 45, precision 220, and
`beta=[1629/16,3259/32]`:

```text
python scripts/certify_surface_g2_trimmed_bulk_lane.py \
  --unit 101p8125_101p84375_trimmed \
  --lo 1629/16 --hi 3259/32
```

The 300-second bounded execution timed out without producing a transcript or
partial rows.  Therefore the pair mean-value collar certificate cannot yet be
joined to a trimmed bulk lane, and the beta gap remains open.  This is a
computational timeout, not a sign counterexample; no headers, hashes, or
manifest entries were fabricated.

A second diagnostic with the neighbouring production orders
`beta_order=30`, `t_order=37`, and `precision=180` also exhausted 300 seconds
without a row.  Thus the timeout is not merely the extra order/precision of
the first attempt; a new algorithmic decomposition is required before this
collar can be made production/replay admissible.

Finally, a beta micro-cell of width `1/128`,
`[1629/16,1629/16+1/128]`, with the same 30/37/180-bit parameters, also
timed out at 300 seconds. Narrowing beta alone therefore does not restore a
usable Lane A computation.
