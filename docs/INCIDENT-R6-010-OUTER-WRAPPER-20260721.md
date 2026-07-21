# Incident: R6 tenth-birth outer wrapper does not enclose the zero-born box

**Date:** 2026-07-21

The isolated R6 implementation
`surface_remainder_delta0_r6_extension_010_cover.py` was run on witness
`parent_000`.  The nominal seventh-order integration completed, but the
call to `surface_remainder_delta0_outer_domain_v7.add_outer_derivatives_box_to`
failed in the annulus evaluator with
`ValueError: leading term in denominator is not nonzero`.

This occurs when the annulus Taylor base is the interval beginning at
`delta_lo=0`.  It is a domain/representation failure of the existing outer
wrapper, not a mathematical counterexample and not a certificate.  The
wrapper and the failed attempt remain isolated from all manifested chains.

The exact-monomial three-witness probe in
`surface_remainder_delta0_r6_exact_three_witness.py` is the permitted design
fallback: it records only the core nominal coefficient and order-five
companion charge.  It explicitly excludes the annulus, spatial outer tail,
and weighted S1'''/S2''' charges.  A future terminal R6 cover must repair this
domain split (or replace it with a proved analytic tail) before any gate can
move.
