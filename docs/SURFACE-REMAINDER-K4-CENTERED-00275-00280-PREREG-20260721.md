# K4 centred band `[0.0275,0.0280]` preregistration

Registered before production. This is a candidate-only continuation of the
centred fixed-domain integrator and carries no K4/G2/G6 or S1'''/S2''' load.

Frozen contract:

```text
unit       k4_00275_00280
delta      [11/400, 7/250]
t          29/10
seed_grid  12
max_cells  9216
precision  140 Arb bits
```

The initial 576-cell design probe was intentionally not used as evidence; it
only identified an adversarial stress. The production/replay pair is required
to be byte-identical and every normalized fraction must be strictly below one.
A failure is a recorded negative design result; a success remains only a
local witness at `t=2.9`, with the global K4 and S1'''/S2''' obligations open.

## Result

Production and replay completed with 9,216 terminal cells and 313 fallback
cells. The byte-identical SHA-256 is
`0601e3ad1a56fc7917df283e4091df6d4592c56593a3171867141a5b5f8611b5`.
The largest normalized fraction is `nuD_main = 0.510108624192872...`; all
seven fractions are strictly below one. The full cell-recomputed validator
passes. This remains a local witness only.
