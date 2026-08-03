# CONTINUUM-C1 repository audit

## Required control documents

Read completely before lane implementation:

- `CLAUDE.md`;
- `CURRENT-STATE.md`;
- `HYPOTHESIS_FRONTIER.md`;
- `README-FOR-NEXT-MODEL.md`.

## Internal evidence used

- `YangMills/L1_GibbsMeasure/TwoPlaquetteCorrelator.lean`:
  `sun_two_plaquette_correlator_bound` and
  `sun_clustering_window_nonempty`;
- `YangMills/L1_GibbsMeasure/RestrictedGate.lean`:
  `normalized_exp_wilson_loop_area_law`;
- thermodynamic-limit and correlation modules under
  `YangMills/L1_GibbsMeasure/`;
- Wilson action, observable, Gibbs measure, gauge marginal, plaquette energy,
  Schur bridge, and fundamental orthogonality modules;
- RG scale/mass/activity modules under `YangMills/RG/`, inspected only as
  consumers or nonmatching producers;
- `AmosClosure/AmosBarrierReal.lean`:
  `amosBoundReal_holds`;
- `AmosClosure/AmosLowerReal.lean`:
  `besselLowerReal_holds`.

The existing lattice spacings in RG are block indices, not a physical
dimensionful `a`. No existing `U(1)` free-boundary factorization theorem was
found. C1 therefore added only its local scale dictionary and did not edit
any inspected module.

The round-two audit found the more fundamental E2 mismatch:

- `AmosClosure/BesselRealInterface.lean` defines `besselIReal` by a
  Γ-power series;
- a `U(1)` Haar computation produces integrals of
  `exp(β cos θ)` against `1` and `cos θ`;
- a filename/content search under the pinned `.lake/packages/mathlib` found
  no Bessel development that identifies those integrals with the Γ-series.

Thus the integral-representation theorem at orders zero and one precedes the
finite-lattice factorization in the dependency order.

## Exact internal mismatch

At `t=ε=1`, the checked KP activity is

```text
exp(|β|N_c)(1+s)-1
```

and the radius hypothesis implies the finite cap proved in C1. The existing
Wilson-loop area law and two-plaquette clustering are volume-uniform inside
this small-coupling window; neither theorem states uniformity along a physical
`a→0` trajectory.

`kpRadiusAtUnit_nonempty_from_checkedWindow` now consumes
`sun_clustering_window_nonempty` directly. This is the compile-time dependency
that prevents the C1 proposition from drifting silently away from the checked
producer. `checkedCorrelatorAfterKPRadiusAtUnit` additionally applies the
actual correlator theorem through its radius argument, guarding against drift
in the consumer even if an obsolete witness theorem remained available.
