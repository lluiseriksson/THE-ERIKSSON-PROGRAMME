# K4 centred band `[0.0285,0.0290]` preregistration

Registered before production. This is a candidate-only continuation of the
centred fixed-domain integrator and carries no K4/G2/G6 or S1'''/S2''' load.

Frozen contract:

```text
unit       k4_00285_00290
delta      [57/2000, 29/1000]
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
