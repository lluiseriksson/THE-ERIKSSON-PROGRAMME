# G2 frontier mid-order diagnostic (2026-07-26)

This is a separate diagnostic, not a replacement for the high-order contract.
It tests whether the timeout is caused by the Taylor enclosure order rather
than by the sign geometry.  The frozen box is
`beta=[1635/16,6541/64]`, `CWIN=3/2`, Arb-180, orders 20/25, and
`MIN_DT=1/100000`, using `scripts/certify_surface_scaled_bulk_cwin3p2_mid_generic.py`.

Any output is candidate-only and cannot promote G2 or G6.  A pass must have a
complete adjacent t cover, strict negative outward endpoints, and a byte
identical replay under the same dependency hashes.  Timeout or failure is
recorded as a design result only.
