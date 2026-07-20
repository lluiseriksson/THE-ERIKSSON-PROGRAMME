# K4 centred band `[0.0280,0.0285]` preregistration

Registered before production. This is a candidate-only continuation of the
centred fixed-domain integrator and carries no K4/G2/G6 or S1'''/S2''' load.

Frozen contract:

```text
unit       k4_00280_00285
delta      [7/250, 57/2000]
t          29/10
seed_grid  12
max_cells  9216
precision  140 Arb bits
```

The isolated wrapper, runner and validator are named with this unit. A
production/replay pair must be byte-identical and the validator must
recompute all seven totals from finite terminal cells, with every normalized
fraction strictly below one. Failure is a negative design result. Success is
only a local witness at `t=2.9`; the regular endpoint, delta/t cover, overlap,
and literal weighted S1'''/S2''' judges remain open.

## Result

Production and replay completed with 9,216 terminal cells and 295 fallback
cells. The byte-identical SHA-256 is
`3efb3348f0a3a7bc11456f7ebf04c95addb26d4fb772b1b89ae147f7277c16d1`.
The largest normalized fraction is `nuD_main = 0.435071099584748...`; all
seven fractions are strictly below one. The validator
`validate_surface_remainder_k4_centered_00280_00285.py` passes. This remains a
local witness only.
