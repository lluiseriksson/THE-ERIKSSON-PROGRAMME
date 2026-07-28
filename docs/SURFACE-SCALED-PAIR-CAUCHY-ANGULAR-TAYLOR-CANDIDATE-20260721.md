# Angular Taylor model for the complex Cauchy route — 2026-07-21

## Scope

`scripts/probe_surface_scaled_pair_cauchy_arc_taylor.py` (SHA-256
`95B361365A49C7F0B693E92ADA7F709AED115B229CAA0CF0D69C686AADBE4FB9`)
forms beta derivatives of the pair-regrouped Wronskian before composing the
complex circle parametrization with an angular Taylor model.  It is a
conditioning probe only: the beta Taylor remainder and Bessel mode tail are
not included.

## Result

At 500 Arb bits, order 24, angular radius `pi/64`, an exhaustive 64-arc
diagnostic cover completed in four isolated processes.  Every angular
interval stayed at the cancellation scale; the maximum printed upper bound
was `1.8124780731788876e-79`.  This is unlike the direct rectangular arc
enclosure, which widened to `~1e-9`.

## Required promotion work

The angular model must be run on an exhaustive fixed arc cover, with a
validated remainder for the omitted beta Taylor terms and a complex Bessel
tail contract.  Until those are present this remains candidate evidence and
does not alter K2, K4, S1'''/S2''', G2, G6, or the manuscript seal.
