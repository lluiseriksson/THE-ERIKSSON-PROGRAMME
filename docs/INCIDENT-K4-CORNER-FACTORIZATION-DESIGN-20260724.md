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
geometric-tail bound for derivatives through order four with respect to `u`,
and a design-only chain-rule enclosure for the fourth-order `TJet`.  This is a
useful analytic ingredient, but it still does not certify the complete carrier
domain, the complement junctions, or the global K4 budget.

The `Jet2` adapter also propagates the scalar tail through its first two
delta-Taylor coefficients.  Its overlap with the legacy carrier was checked
at a high-`z` scalar box, but the adapter remains quarantined and is not wired
into any authoritative transcript.

## Measured effect

At two representative interval boxes, the finite 80-term diagnostic series
remained finite and reduced the printed radius of the carrier charges by
roughly one to four orders of magnitude.  The result is only a conditioning
measurement: the implementation has no certified series tail or fourth-order
derivative remainder, so these numbers cannot enter a production transcript.

For compatibility with the actual K4 smoke, a separate `Jet2` adapter was
also exercised by monkey-patching only the smoke's carrier functions.  At the
registered stress point it was finite on the 16-, 24-, and 32-grid runs; the
32-grid radii were approximately `8.52, 0.387, 2.71` for the main charges and
`5.39, 3.46, 1.51, 0.850` for the mirror charges.  These are raw summed
second-coefficient radii, not the final weighted budgets, and the run was not
production/replay paired.  The 8-grid run still produced non-finite main
charges, so this is a conditioning result rather than a K4 certificate.

A four-point t sweep at grid 16 exposes the remaining obstruction.  At
`t=2.9` the factorized mirror radii are moderate, but at `t=1.5` they reach
about `1.4e11` and at `t=0.589` about `1.9e18`; the latter also has 14
inadmissible cells.  Thus eliminating `sqrt(R^2)` removes one dependency but
does not control the mirror exponential uniformly near the small-t seam.
That seam needs a separate chart or a direct positive majorant.

The numerical paragraph above predates the algebraic correction below and is
therefore superseded.  A fresh corrected point-grid sweep is recorded by
`scripts/probe_surface_k4_corner_corrected_sweep.py`.  At `delta=[0.01,0.0105]`
and a 16-by-16 midpoint grid, the summed `MD_mirror` second-coefficient
charges are approximately `1.98e-47` (`t=2.9`), `2.32e-21` (`t=1.5`),
`1.99e2` (`t=0.8`), and `1.00e10` (`t=0.589`).  This is a midpoint
conditioning diagnostic, not an interval enclosure; it confirms that the
small-`t` seam remains uncontrolled even after fixing the series identity.

## Required proof obligations before integration

1. Bound the series tail uniformly on the complete K4 `u` domain.
2. Bound the first four derivatives in the delta/Taylor algebra, including the
   derivative of `u` and the exponential factor.
3. Replay the resulting Jet enclosure against an independently generated
   production transcript and compare it with the pre-registered K4 budgets.

Until all three obligations are discharged, the authoritative K4/H_tail and
G2/G6 gates remain unchanged and the manuscript seal remains blocked.

## Algebraic correction (2026-07-24)

An independent coefficient audit found and corrected a design-prototype bug:
the implementation had declared `u=(beta R)^2` while using the coefficients for
the natural variable `z^2/4`. Consequently its omitted factors were inflated
by `4^k`, so the prototype evaluated the wrong Bessel quotients. The module
now uses `u=(beta R)^2/4` consistently in all four adapters. The exact audit
is `scripts/verify_surface_corner_series_identity.py` and passes for the first
coefficients and derivative-tail ratios. This correction is confined to the
design-only module; it does not alter any authoritative transcript or gate,
and it does not provide a K4 certificate.
