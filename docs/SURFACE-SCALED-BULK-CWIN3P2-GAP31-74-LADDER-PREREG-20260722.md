# Preregistration: width-`1/16` CWIN=3/2 ladder on `[31,74]`

**Date:** 2026-07-22  
**Scope:** candidate finite-beta relay evidence; no automatic G2/G6 promotion.

The three-cell pilot in `SURFACE-SCALED-BULK-CWIN3P2-GAP31-74-PILOT-PREREG-20260722.md`
passed at the lower edge, midpoint, and upper edge.  This preregisters the
next contiguous ladder with fixed beta width `1/16`:

```text
beta boxes [31 + j/16, 31 + (j+1)/16],  j = 0,...,687
```

The first two boxes overlap already archived quarter-cell witnesses and are
retained as the same geometric partition; any overlapping pilot manifest is
quarantined rather than counted twice.  Every other box is a new production /
fresh-replay pair under the frozen contract:

```text
CWIN=3/2, beta_order=30, t_order=37, min_dt=1/100000, Arb precision=180
t-domain [3/5, pi - (3/2)/beta_lo]
```

Acceptance is per box: finite strictly negative outward-rounded upper
endpoints, adjacent terminal `t` rows reaching the seam, byte-identical
production/replay, current dependency hashes, and an owning manifest.  A
failed box is retained as a terminal incident; no adaptive widening, rescue,
or relabelling is permitted under this registration.

This ladder remains candidate evidence.  Sign rows alone do not prove
`(H_tail)`; the exact Wronskian relay and the independent claim audit must
still be green before any G2/G6 promotion.
