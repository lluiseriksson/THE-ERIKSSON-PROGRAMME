# Direct complex-arc enclosure rejected — 2026-07-21

The Cauchy-circle probe was extended from point samples to 64 rectangular Arb
arc enclosures.  Although the point samples stay near `1e-79`, the direct
rectangle evaluation loses the shared beta dependence: the resulting upper
bounds are approximately `5.1e-9` to `6.3e-9`.

This is a conditioning failure of the enclosure, not a sign result.  The
rectangle route is rejected.  A successful Cauchy implementation must use a
Taylor model in the angular parameter (or a separately proved derivative
bound) before interval summation.  No G2/G6 state changes.

