# CWIN=3/2 scaled-bulk width-1/4 continuation II

**Status:** preregistered candidate design only; no G2/G6 load.

The frozen backend remains `CWIN=3/2`, beta order 30, t order 37, minimum t
width `1/100000`, and 180 Arb bits.  The four independent boxes are

```text
[637/16,641/16], [641/16,645/16], [645/16,649/16], [649/16,653/16].
```

Each requires fresh production and replay, exact contiguous t coverage, and
strictly negative outward Arb upper endpoints.  These are candidate sign rows
only; they do not imply `(H_tail)` or promote G2/G6.
