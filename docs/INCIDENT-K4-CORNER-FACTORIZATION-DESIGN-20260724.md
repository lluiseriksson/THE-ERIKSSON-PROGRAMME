# K4 corner-carrier factorization design probe (2026-07-24)

**Status:** `DESIGN_ONLY`; no K4, `S1'''/S2'''`, G2, or G6 promotion.

## Exact algebraic observation

The scaled carrier contains the product

\[
 e^{-z}\frac{I_n(z)}{z^n}\,e^{z-4\beta c}
   =e^{-4\beta c}\frac{I_n(z)}{z^n},
 \qquad z=\beta R.
\]

The design module `scripts/surface_remainder_corner_carrier_design.py` evaluates
the right hand side with

\[
 \frac{I_1(z)}z=\sum_{k\ge0}\frac{(z^2/4)^k}{2k!(k+1)!},
 \qquad
 \frac{I_2(z)}{z^2}=\sum_{k\ge0}\frac{(z^2/4)^k}{4k!(k+2)!},
\]

using the polynomial variable `u=(βR)^2`.  This removes the explicit
`sqrt(R^2)` and the cancellation between two exponentials from the diagnostic
expression.

The same module now contains `ratio_tail_majorants`, an explicit positive
geometric-tail bound for derivatives through order four with respect to `u`.
It is a useful scalar ingredient, but it does not yet compose the chain rule
for `u(δ)` or certify the complete fourth-order Taylor jet.

## Measured effect

At two representative interval boxes, the finite 80-term diagnostic series
remained finite and reduced the printed radius of the carrier charges by
roughly one to four orders of magnitude.  The result is only a conditioning
measurement: the implementation has no certified series tail or fourth-order
derivative remainder, so these numbers cannot enter a production transcript.

## Required proof obligations before integration

1. Bound the series tail uniformly on the complete K4 `u` domain.
2. Bound the first four derivatives in the delta/Taylor algebra, including the
   derivative of `u` and the exponential factor.
3. Replay the resulting Jet enclosure against an independently generated
   production transcript and compare it with the pre-registered K4 budgets.

Until all three obligations are discharged, the authoritative K4/H_tail and
G2/G6 gates remain unchanged and the manuscript seal remains blocked.
