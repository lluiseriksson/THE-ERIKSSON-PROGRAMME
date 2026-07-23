# K4 complement carrier diagnostic — 2026-07-23

This note records a quarantined diagnostic, not a theorem certificate.

## Question

The low-z carrier adapter replaces the historical `a_scaled_jet` and
`b_scaled_jet` formulas by positive entire-series derivative enclosures only
when the complete Arb box satisfies `0 <= z <= 4`. A box crossing `z=4` is
delegated to the historical implementation; no branch splice is performed.

## Result

The adapter was run in a fresh process against the fixed-domain L3 design
smoke at `delta=1/15`, `t=2.9`, grids 32 and 64. Both runs were finite:

* grid 32: `muF_main=[2e+1 +/- 8.96]`, `nuD_main=[+/- 1.37]`;
* grid 64: `muF_main=[2e+1 +/- 2.35]`, `nuD_main=[-0.8 +/- 0.0711]`.

However, the adapter counters recorded **zero** low-z calls and all
carrier evaluations fell back to the historical branch. A 16-grid diagnostic
measured the observed `z` range as approximately `[10.916, 40.385]`.
Therefore this experiment does not improve the K4 enclosure: the stress
complement is outside the adapter's low-z domain. It is retained as a
negative diagnostic so that the low-\z series cannot be mistaken for a
global repair.

## Reproducibility and rejection criteria

The adapter is isolated in
`scripts/surface_remainder_carrier_jet_lowz_candidate.py`, with tests in
`tests/test_surface_remainder_carrier_jet_lowz_candidate.py`. The tests check
the closed low-z branch and reject boxes crossing `z=4`. No historical
carrier module or authoritative manifest is modified. This evidence carries
no promotion for K4, S1'''/S2''', G2, or G6.
