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
The byte-separate successor
`surface_remainder_delta0_outer_domain_r6split.py` now repairs this specific
failure by recursively subdividing the delta base interval and summing
outward absolute coefficient bounds; a smoke call on the failing box returns
six finite rows.  This repair has not yet been run through the three-witness
R6 judge or a production/replay cover.

An exact-monomial source was then paired with the split wrapper on witness
`parent_000`.  The nominal coefficient is finite (`1677.309`), but the
registered direct moving-band charge is `303182.034`, giving a strict
negative R6 margin (`-297259.343`) against `7600`.  This is a genuine
failure of the present outer-band majorant, not evidence that the theorem is
false; a sharper analytic band bound is required before the R6 head can be
promoted.

The exact-monomial three-witness probe in
`surface_remainder_delta0_r6_exact_three_witness.py` is the permitted design
fallback: it records only the core nominal coefficient and order-five
companion charge.  It explicitly excludes the annulus, spatial outer tail,
and weighted S1'''/S2''' charges.  A future terminal R6 cover must repair this
domain split (or replace it with a proved analytic tail) before any gate can
move.
