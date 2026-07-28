# K2 KD-covariance design results

**Date:** 2026-07-28

**State:** design evidence only; no K2, K4, S1/S2, gate, or manuscript
promotion.

## Corrected grid-48 conditioning probe

After correcting the Grüss charge documented in
`INCIDENT-K2-KD-COVARIANCE-GRUSS-FACTOR-20260728.md`, the unchanged
pre-registered grid-48 predicate passes:

```text
KD mass lower > 0
Y radius = 0.2978629106655717 < 1
closed-form target overlap = true
terminal = KD COVARIANCE GRID48 DESIGN PASS; NO K2 PROMOTION
```

The authoritative transcript SHA-256 is
`6E5DD1B2CD334872B3CD6F046EDBCB59A720344D32A4D2419EC95F7A00548DC2`
for the raw CRLF file and
`8E50F24BAB17DDCCB590FC76DB00619D435FEB9B594BF80EC205F23FA54E1F25`
after LF normalization.
Its stderr file is empty.  The superseded pre-correction transcript is
preserved with SHA-256
`8A1E65F310E8A2B39C1426D47D41C22595C819F0DACE0027DFA7DFD0FEC1FBAF`.

This confirms that the KD-weighted covariance coordinate materially improves
the zeroth-order stress-cell conditioning.  It does not bound a positive
delta remainder.

## Direct coefficient-series probe

The separately pre-registered coefficientwise second-spatial-derivative
integrator fails its grid-24 target:

```text
radius(Y0) = 4.12944
radius(Y1) = 155.036
radius(Y2) = 4295.84
radius(Y3) = 115841.11 > 1968
terminal = KD COVARIANCE SERIES DESIGN FAIL; NO K2 PROMOTION
```

All four intervals overlap the exact heads, so this is enclosure dependency,
not contrary sign evidence.  The transcript SHA-256 is
`21F5B1D72A6645E3D80376833F55924D7D91797E6267EA1D5B431440ED56AE54`
for the raw CRLF file and
`150077C11E02140BF8A10E78F6356242A78C8508DAADA01D499BCE5DBCF15767`
after LF normalization.
Blind refinement of this direct coefficientwise second-order architecture is
retired.  A successor must either retain the between/within covariance
structure at the remainder level, integrate at higher spatial order, or
prove a separate analytic tail lemma after subtracting the exact heads.
