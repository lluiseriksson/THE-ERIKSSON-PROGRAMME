# Exploratory beta-motion probe near the post-1635 obstruction

Date: 2026-07-25. This is an exploratory diagnostic, not a preregistered
certificate and not admissible for G2/G6 promotion.

Using Arb-180, beta/t orders `30/37`, CWIN `3/2`, `MIN_DT=1/100000000`, and
the same `t` interval `[3.122,3.124]`, three narrow beta boxes of width
`1/1024` were tested:

```text
beta [1635/16, 1635/16+1/1024]  PASS, 4 rows, endpoint 781/250
beta [3271/32-1/1024, 3271/32]  PASS, 15 rows, endpoint 781/250
beta [6543/64, 6543/64+1/1024]  FAIL near t=3.1233782043457032
```

The first two boxes are local interval successes; the third reproduces an
obstruction shifted in `t`. This is consistent with a beta-dependent moving
hard point, but it does not prove that interpretation: the changed beta boxes
also change enclosure widths and subdivision paths. No global coverage or
relay conclusion follows, and the authoritative G2 state remains blocked.
