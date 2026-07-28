# CWIN=3/2 scaled-bulk width-1/4 continuation III

**Status:** preregistered candidate design only; no G2/G6 load.

Frozen configuration: `CWIN=3/2`, beta order 30, t order 37, minimum t width
`1/100000`, and 180 Arb bits.  The four boxes are

```text
[653/16,657/16], [657/16,661/16], [661/16,665/16], [665/16,669/16].
```

Each box requires independent production/replay, exact contiguous t coverage,
and strictly negative outward Arb upper endpoints.  These sign rows remain
candidate-only and do not imply `(H_tail)` or promote G2/G6.
