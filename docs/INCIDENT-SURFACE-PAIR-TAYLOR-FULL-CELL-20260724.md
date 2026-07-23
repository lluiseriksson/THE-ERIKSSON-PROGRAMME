# Pair-Taylor full-cell design probe — dependency wall

**Date:** 2026-07-24  
**Scope:** design-only; no K2/G2/G6 promotion

The exact pair-grouped Taylor prototype was evaluated on the difficult seam
cell
`beta=[1629/16,3259/32]`, `lambda=[3/2,19/10]` twice:

- order `(24,24)`, 120 modes, 500 Arb bits;
- order `(50,50)`, 160 modes, 700 Arb bits.

Both runs returned the same interval enclosure for the finite grouped part,
approximately `+/-1.53e-108`; increasing order only reduced the explicit mode
tail from about `1e-119` to `1e-197`. The sign loss is therefore interval
dependency in the full beta/lambda box, not merely the finite-mode tail.

The result rules out this unmodified full-cell Taylor route as a closure
mechanism. It does not refute the pointwise pair identity or the Surface
Theorem, and it leaves the relay and all gates unchanged.
