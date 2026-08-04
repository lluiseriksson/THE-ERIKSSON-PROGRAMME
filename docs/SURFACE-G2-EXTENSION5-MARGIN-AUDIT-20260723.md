# Extension-5 normalized-sign margin audit

**Status:** diagnostic only; quarantined; no G2/G6 or `(H_tail)` promotion.

The order-24/CWIN-`3/2` extension-5 manifest covers 16 beta units,
`[259/4,275/4]`, with 3,980 accepted `t` rows and byte-identical production
and replay transcripts.  The read-only parser
`scripts/audit_surface_scaled_bulk_extension5_margins.py` extracts the
outward-rounded `upper` interval endpoint from each row and reports its
positive distance from zero.

The smallest normalized-sign margin is

```text
6.479612977592499209870774056903679550763...e-77
```

at unit 79, `trow 260`, whose recorded row is
`t ∈ [207314003061/66560000000, 2904688892211/931840000000]`.
The interval endpoint is `-6.4796...e-77` with radius `3.00e-158`.

This number is evidence about `W^J` only.  It does not bound the absolute
`H_tail`: the repository's exact scaling identity preserves the sign of the
Wronskian while the separate weighted derivative/tail majorant can change.
Consequently the authoritative audits remain `RELAY_LEMMA_UNPROVED`,
`M_SUPREMUM UNSUPPLIED`, and final seal blocked.  The next relay experiment
must emit a certified positive rescaling bound and an absolute tail budget;
the sign-margin table alone cannot do that.
