# Pair-Taylor candidate for the scaled bulk seam — 2026-07-21

## Scope

This is a registered engineering probe, not a G2/G6 certificate.  It tests
whether the open beta seam can be evaluated after the exact pair identity is
formed before interval summation:

`W = 2 sum_{m<n} (a_m b_n-a_n b_m) K_{mn}(t)`.

The candidate scripts are:

* `scripts/probe_surface_scaled_pair_taylor_point.py`, SHA-256
  `492580C9924D538BAF2AD6F3930F2B0A4AAD9FE41AB6D5CE248478BC74A00C52`;
* `scripts/probe_surface_scaled_pair_taylor_box.py`, SHA-256
  `10E9C95E581BDD7FC6CBB90124629E4F9F33FEEA1D73ED8F97833C2AB7B06239`.

## Reproducible candidate result

At 500 Arb bits, the beta box
`[1629/16, 1629/16+1/16]` and the t cell
`[1311/500, 1311/500+1/1000]` gave

`W = -1.3684535880997e-79 +/- 2.96e-93`.

The finite pair Taylor polynomial, t remainder, and omitted-mode bound were
all included in that displayed enclosure.  The result is strictly negative.

## Why this is not yet promotable

Historically, the beta remainder used the highest reconstructed beta
derivative as a proxy for the next derivative order; that route was explicitly
candidate-only.  The 2026-07-22 repair replaces the separate lambda-slope
heuristic by an explicit derivative majorant, but a terminal backend must
still certify the full order-`q+1` contract, carry the moving-t cover, and
replay the whole interval `[1629/16,1000/9]`.  Until those items exist, G2 and
G6 remain unchanged.

## Engineering conclusion

The pair regrouping is viable at the difficult scale: increasing precision to
500 bits and forming the pair kernel before summation recovers a strict margin
where the direct Fourier Taylor enclosure was zero-centred.  The 2026-07-22
repair removes the separate lambda-slope heuristic; the remaining work is a
proved full order-`q+1` beta derivative-tail contract and a preregistered
finite cover.

## 2026-07-22 remainder repair

The former heuristic contribution `100*lambda_remainder` in the beta-slope
remainder has been removed.  The replacement is an explicit positive
majorant for the beta derivative of the lambda remainder: the product rule is
applied to the two coefficient products in each pair minor, and
`d/d beta (k/beta)^(L+1)` is bounded with the exact lower endpoint of the beta
box.  The implementation is in
`scripts/surface_scaled_pair_taylor_remainder_design.py`; the cell driver
records the resulting `lambda_beta_remainder` row.

The first adversarial cell after the continuous candidate segment,
`beta=[101.96875,101.984375]`, `lambda=[1.5,1.9]`, was rerun at 500 Arb bits
in separate production and replay processes.  Both transcripts are byte
identical and validate with
`total_upper = -3.196183918960269...e-109`.

The manifest is
`run-manifests/surface-scaled-pair-mean-value-gap-cell-20260722.json`.
This is a checked single-cell candidate, not a G2 promotion: the remaining
beta interval, moving-t cover, scaled-tail splice, and global relay are still
open.

The same repaired production/replay contract also closes the adjacent cell
`beta=[101.984375,102]`, `lambda=[1.5,1.9]`, with
`total_upper = -3.072363298465311...e-109`.  The two-cell candidate cover is
manifested in `run-manifests/surface-scaled-pair-mean-value-gap-cover-20260722.json`;
it remains local evidence and does not promote G2.

The same repaired backend was then split at the former order-60 failure
`[102.4375,102.5]`.  At beta order 80, modes 115, lambda order 50 and 500
Arb bits, both half-cells passed in independent production/replay processes:

* `[102.4375,102.46875]`, with `total_upper = -5.372368728149817...e-110`;
* `[102.46875,102.5]`, with `total_upper = -4.339696063927147...e-110`.

The byte-equal transcripts and their manifest are recorded in
`run-manifests/surface-scaled-pair-mean-value-gap-cover-beta102p4375-102p5-order80-20260722.json`.
These are still candidate cells only: no moving-`t` cover, scaled-tail splice,
global relay, or G2/G6 promotion is claimed.

One further adjacent cell, `[102.5,102.53125]` at the same lambda box and
configuration, also passed production/replay with
`total_upper = -3.338071158877775...e-110`.  Its current-head transcript pair
and hash are recorded in
`run-manifests/surface-scaled-pair-mean-value-gap-cell-beta102p5-102p53125-order80-20260722.json`.
The cell is deliberately isolated because the preceding two-cell manifest was
produced at the prior clean head; this preserves exact provenance rather than
silently mixing executions.
