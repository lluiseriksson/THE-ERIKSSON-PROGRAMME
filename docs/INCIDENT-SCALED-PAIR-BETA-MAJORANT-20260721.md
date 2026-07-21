# Positive beta-majorant route rejected — 2026-07-21

## Scope

The script
`scripts/probe_surface_scaled_pair_beta_majorant.py` (SHA-256
`882E6CB94D0F7C57CBC9B211507C8A3597F931F7ABE0397BF61342F471529777`)
measures the standard positive Bessel-monomial bound for the order-25 beta
remainder of the pair-regrouped Wronskian on
`[1629/16, 1629/16+1/16]`.

## Result

At 220 Arb bits it reports

* positive derivative majorant: `8.763085448618677e23`;
* induced Taylor remainder: `1.3281952100252968e-39`.

The useful Wronskian on the stress cell is approximately `1e-79`, so this
bound loses about forty orders of magnitude and cannot certify a sign.

## Decision

This route is rejected and carries no G2/G6 load.  It proves that the next
backend must preserve beta cancellation in the remainder itself (for example
through a ratio/determinant representation or a validated analytic majorant),
not merely regroup the central finite Taylor polynomial.

