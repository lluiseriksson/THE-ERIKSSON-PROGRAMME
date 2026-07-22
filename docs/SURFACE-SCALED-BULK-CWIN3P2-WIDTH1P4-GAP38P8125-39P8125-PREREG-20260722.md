# CWIN=3/2 scaled-bulk width-1/4 continuation

**Status:** preregistered candidate design only; no G2/G6 load.

This continuation freezes the same backend and acceptance rules as the
preceding width-1/4 pilot: `CWIN=3/2`, beta order 30, t order 37, minimum t
width `1/100000`, and 180 Arb bits.  The four independent beta boxes are

```text
[621/16,625/16], [625/16,629/16], [629/16,633/16], [633/16,637/16].
```

Every box requires independent production and replay, byte-identical
transcripts, exact contiguous t coverage, and strictly negative outward Arb
upper endpoints.  A pass is candidate evidence only; no result implies
`(H_tail)` or promotes G2/G6.
