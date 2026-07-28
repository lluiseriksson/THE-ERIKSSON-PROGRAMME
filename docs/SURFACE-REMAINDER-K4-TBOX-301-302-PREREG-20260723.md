# K4 fixed delta/t continuation — `[3.01,3.02]`

**Registered:** 2026-07-23, before the production/replay pair

Frozen continuation immediately adjacent to the registered box
`[3,301/100]`.  Parameters are unchanged:

```text
delta = [1/25,81/2000] = [0.04,0.0405]
t     = [301/100,151/50] = [3.01,3.02]
seed_grid = 12; max_cells = 2304; Arb precision = 140 bits
```

Both runs must use `scripts/certify_surface_remainder_k4_t_box_probe.py`,
contain exactly 2,304 cells, pass the seven-row validator, and agree byte for
byte.  A failure is terminal for this frozen unit.  A success remains
candidate-only and supplies no global K4, S1'''/S2''', or G6 promotion.

