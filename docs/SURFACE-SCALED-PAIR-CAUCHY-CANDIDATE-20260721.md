# Complex-circle Cauchy candidate for the scaled beta remainder — 2026-07-21

## Scope

This is a diagnostic candidate, not a G2/G6 certificate.  The executable
`scripts/probe_surface_scaled_pair_cauchy_circle.py` (SHA-256
  `B5BD9A716AEF132D33E46194040E227C649882746BC1E98D75AABB5AACC5BB9F`)
evaluates the finite pair-regrouped Wronskian at 64 points on

`|beta - 101.84375| = 0.1`, `t = 2.6225`, `M = 160`, `500` Arb bits.

## Result

The sampled absolute upper bounds range from approximately
`1.297e-79` to `1.8114e-79`.  For the local beta half-width
`H=1/32`, order `p=24`, and radius `R=0.1`, the formal Cauchy estimate based
on the sampled maximum is

`M*(H/R)^(p+1)/(1-H/R)`, approximately `5e-92`.

This is small enough to preserve the observed negative central margin.  It is
the first route that keeps the beta remainder at the same cancellation scale
as the Wronskian instead of replacing it by the rejected positive majorant.

## Missing terminal ingredients

The 64 angular samples are not a supremum proof.  A direct rectangular Arb
enclosure of those arcs was also tested and loses cancellation (upper bounds
of order `1e-9`), so it cannot be used.  A terminal implementation must
provide a Taylor/derivative-preserving Arb arc cover (or an equivalent
rigorous angular derivative bound), a
complex Bessel tail bound for all omitted modes, and a production/replay
transcript with exact dependency hashes.  Until those are present this note
does not change G2, K2, K4, S1'''/S2''', or G6.
