# K4 fixed delta/t continuation — `[3,3.01]`

**Registered:** 2026-07-23, before the production/replay pair

This is an isolated continuation of the candidate fixed-physical K4
integrator.  It is intentionally not a gate promotion and cannot alter the
regular-ball, overlap, or global weighted-judge requirements.

Frozen parameters:

```text
delta = [1/25,81/2000] = [0.04,0.0405]
t     = [3,301/100] = [3,3.01]
seed_grid = 12
max_cells = 2304
Arb precision = 140 bits
```

The production and replay runs must use the unchanged driver
`scripts/certify_surface_remainder_k4_t_box_probe.py`, record all dependency
hashes, contain exactly 2,304 terminal cells, and pass the literal seven-row
fraction validator.  Any failure is retained as a negative result; no mesh,
width, or budget may be changed after reading the result.

Even a successful pair remains candidate-only.  It supplies no regular
`delta=0` patch, no complete `t` union, no overlap theorem, and no global
S1'''/S2''' or K4 promotion.

