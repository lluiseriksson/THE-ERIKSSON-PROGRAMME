# CWIN=3/2 scaled-bulk width-1/4 continuation IV

**Status:** preregistered candidate design only; no G2/G6 load.

Frozen configuration remains `CWIN=3/2`, beta order 30, t order 37, minimum t
width `1/100000`, and 180 Arb bits.  The four boxes are

```text
[669/16,673/16], [673/16,677/16], [677/16,681/16], [681/16,685/16].
```

Each requires independent production/replay, exact contiguous t coverage, and
strictly negative outward Arb upper endpoints.  These rows are candidate-only;
they do not imply `(H_tail)` or promote G2/G6.
