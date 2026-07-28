# CWIN=3/2 scaled-bulk width-1/4 pilot

**Status:** preregistered candidate design only; no G2/G6 load.

This pilot tests whether the current high-order backend can certify wider
beta boxes without changing any analytic constant.  The frozen configuration
is `CWIN=3/2`, beta Taylor order 30, t Taylor order 37, minimum t width
`1/100000`, and 180 Arb bits.  The first box is

```text
beta in [617/16, 621/16] = [38.5625,38.8125].
```

The production and replay must be independent subprocesses with byte-identical
transcripts, exact contiguous t coverage, and strictly negative outward Arb
upper endpoints.  A pass is candidate evidence only.  A failure retires this
width-1/4 pilot and does not alter the width-1/16 ladder or any gate state.
No result from this pilot may promote G2/G6 or imply `(H_tail)`.
