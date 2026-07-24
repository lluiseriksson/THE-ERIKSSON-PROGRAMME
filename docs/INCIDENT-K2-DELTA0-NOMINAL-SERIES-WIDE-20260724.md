# Incident — nominal delta-jet enclosure is too wide at the zero lane

**Date:** 2026-07-24  
**Scope:** K2 design route only; no K2, G2, G6, or manuscript promotion.

## Reproduction

Using `scripts/surface_remainder_delta0_series_design.py` with the registered
finite square (`side=12`) and a zero base lane, the call

```text
normalized_y_derivative_enclosure(arb("0"), arb("2.90"), grid=24, side=12)
```

returns normalized derivative balls with displayed radii approximately

```text
[9.78e1, 9.58e3, 9.11e5, 8.63e7].
```

Replacing the exact zero lane by `0 +/- 1e-6` fails before producing a
series: Arb cannot prove the leading denominator term nonzero in the series
division.  Increasing the grid does not repair this structural conditioning
problem; it is a denominator/jet enclosure issue, not evidence about the
truth of K2.

## Consequence

The explicit low-order algebra and finite-box moment containment remain valid,
but they do not supply the L1 Taylor-with-remainder lemma required by the
registered direct contract.  A terminal route must introduce a cancellation-
preserving factorization or a separately proved denominator lower bound before
using this jet.  Until then the K2 gate remains open and the manuscript slot
must remain present.
