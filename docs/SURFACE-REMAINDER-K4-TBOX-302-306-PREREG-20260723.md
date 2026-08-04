# K4 fixed delta/t continuation batch — `[3.02,3.06]`

**Registered:** 2026-07-23, before this batch

Four exact adjacent units are frozen:

```text
[151/50, 303/100], [303/100, 76/25],
[76/25, 153/50],   [153/50, 61/20]
```

Together they cover `[3.02,3.06]`.  Every unit uses
`delta=[1/25,81/2000]`, `seed_grid=12`, `max_cells=2304`, and 140 Arb bits.
Each production/replay pair must contain exactly 2,304 cells, pass the seven
literal fraction validator, and be byte-identical.  A failed unit is retained
without changing any parameter.  A successful batch remains candidate-only:
it supplies no regular endpoint, complete `t` union, overlap theorem, or
global K4/S1'''/S2'''/G6 promotion.

