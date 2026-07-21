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
  `59B9BB0A007B25364AA9F63C983CF1366421FB240669CB43B6B266B7E17F1454`.

## Reproducible candidate result

At 500 Arb bits, the beta box
`[1629/16, 1629/16+1/64]` and the t cell
`[1311/500, 1311/500+1/1000]` gave

`W = -1.4798130213532752712766267354e-79 +/- 1.50e-108`.

The finite pair Taylor polynomial, t remainder, and omitted-mode bound were
all included in that displayed enclosure.  The result is strictly negative.

## Why this is not yet promotable

The beta remainder currently uses the highest reconstructed beta derivative as
a proxy for the next derivative order; it is therefore explicitly
candidate-only.  A terminal backend must derive and certify the order
`q+1` derivative-tail bound, carry the full moving t cover, and replay the
whole interval `[1629/16,1000/9]`.  Until those three items exist, G2 and G6
remain unchanged.

## Engineering conclusion

The pair regrouping is viable at the difficult scale: increasing precision to
500 bits and forming the pair kernel before summation recovers a strict margin
where the direct Fourier Taylor enclosure was zero-centred.  The next
implementation step is to replace the proxy beta remainder with a proved
derivative-tail contract, then run a preregistered finite cover.
