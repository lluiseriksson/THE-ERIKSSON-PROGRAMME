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

The next falsifiable step is a parameter-width pilot using the same fixed
spatial partition logic.  If the point margin is consumed by arbitrarily
small `(delta,t)` widths, the second-order spatial enclosure architecture is
rejected and must be replaced by a higher-order local Taylor model.  A point
mesh increase alone is not a G2 completion strategy.
