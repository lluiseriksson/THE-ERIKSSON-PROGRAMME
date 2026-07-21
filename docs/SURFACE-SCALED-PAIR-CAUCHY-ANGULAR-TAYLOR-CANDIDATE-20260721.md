# Angular Taylor model for the complex Cauchy route — 2026-07-21

## Scope

`scripts/probe_surface_scaled_pair_cauchy_arc_taylor.py` (SHA-256
`A44E5C0E6319DE0154D3873CC2EEA45C0688D0585F0CA880466A2FD61DDF6ED1`)
forms beta derivatives of the pair-regrouped Wronskian before composing the
complex circle parametrization with an angular Taylor model.  It is a
conditioning probe only: the beta Taylor remainder and Bessel mode tail are
not included.

## Result

At 500 Arb bits, order 24, angular radius `pi/64`, eight diagnostic arc
centres gave interval upper bounds between approximately
`1.3184e-79` and `1.7963e-79`.  A single full arc interval was also strictly
at that scale, unlike the direct rectangular arc enclosure, which widened to
`~1e-9`.

## Required promotion work

The angular model must be run on an exhaustive fixed arc cover, with a
validated remainder for the omitted beta Taylor terms and a complex Bessel
tail contract.  Until those are present this remains candidate evidence and
does not alter K2, K4, S1'''/S2''', G2, G6, or the manuscript seal.

