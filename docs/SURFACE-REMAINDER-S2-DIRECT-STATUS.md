# Direct joint-remainder route — current status

**Date:** 2026-07-12

**Gate:** G2 remains `OPEN_DESIGN`

The first post-registration Arb point run completed at the registered
stress location `t=2.9`, with the candidate threshold `beta=20`:

```text
effective cells     65,536
Y                   [0.39 +/- 4.09e-3]
absolute residual   <= 0.00501633856846
Theta3/beta^2       >= 0.00716017174363
certified margin    >= 0.00214383317516
verdict              DESIGN_POINT_PASS
```

The transcript is owned by
`s2-direct-point-20260712T073531Z.json`.  It proves the inequality at one
point only.  It does not cover a beta interval, a t interval, or the analytic
`delta=0` endpoint, so it carries no theorem load.
The exact executed dependency is preserved as
`scripts/archive/surface_remainder_y_integrator_3593648d.py`; later
development of the live integrator cannot rewrite the run's provenance.

## Parameter-width and coordinate pilots

The natural-interval parameter pilot is rejected.  At 16,384 spatial cells,
even `(Delta beta,Delta t)=(0.001,0.0001)` widened `Y` to `+/-0.646`, far
outside the budget.  The code now has a loud forced-subdivision depth floor;
the earlier unbounded recursion on a non-finite box is no longer possible.

Exact automatic t-jets were then checked against independent multiprecision
differentiation in both Bessel lanes.  For a t-box of width `0.001`, the
Taylor contributions at the stress point are sized by

```text
|Y_t| radius contribution       <= 3.7e-5
|Y_tt/2| radius^2 contribution  <= 1.5e-6
```

so the parameter-Taylor route survives.  A second attempted improvement,
Gaussian extraction on the fixed scaled square
`[0,(6/5)sqrt(20)]^2`, is rejected: the value radius contracted only
`2.48 -> 2.13 -> 1.97` on the `1024 -> 4096 -> 16384` ladder.  This is not
a certificate architecture.

The active next step is therefore a bivariate parameter Taylor cover whose
central values use the physical-square integrator, with derivative bounds on
smaller boxes.  A point mesh increase or a natural parameter interval alone
is not a G2 completion strategy.

At the minimum-budget bulk edge `(t,beta)=(0.6,20)`, the 65,536-cell
physical-square judge failed with margin `-0.00132402`; the next quadtree
level, 262,144 cells, passed with residual upper `0.00113777`, budget
`0.00269140`, and margin `+0.00155363`.  A binary longest-axis variant at
65,536 leaves was both slower (`704 s` versus `441 s`) and wider (margin
`-0.00152511`), so it is rejected and not retained in the production code.
