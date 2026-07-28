# R6 determinant-gauge cancellation: design result (2026-07-24)

**Status:** `DESIGN_ONLY`; no K2, `(H_tail)`, G2, or G6 promotion.

## Purpose

The annulus-inclusive componentwise R6 probe on the first born `t` box
failed the registered `7600` budget: its lower margin was
`-12055.174760783...`.  The failure is caused by taking absolute moment
majorants before forming the bilinear numerator.  A separate signed sum
preserved the nominal cancellation, but it was not a terminal carrier and
became unusable near the right edge.

## Exact identity

With

\[
 N=K_D H_{DF}-K_F H_{DD},
\quad K_D=\int KD,\quad K_F=\int KF,
\quad H_{DD}=\int HD^2,\quad H_{DF}=\int HDF,
\]

the substitution `F~ = F - lambda D` gives, for every scalar `lambda`,

\[
 N=K_D(H_{DF}-\lambda H_{DD})
       -(K_F-\lambda K_D)H_{DD}.
\]

This was checked symbolically and by evaluating both forms in the diagnostic
carrier.  It uses no sign implication and no comparison of two quadratures.
Equivalently, the numerator has the exact double-integral form

\[
 N=\iint K(x)H(y)D(y)\,[D(x)F(y)-F(x)D(y)]\,dx\,dy.
\]

## Independent falsification of the coarse route

The diagnostic
`scripts/probe_surface_remainder_r6_gauge_box.py` was run on born box 0,
`t\in[0,1/50]`, with the signed annulus contribution.  It selected the
midpoint minimizer of the two leading ratios and reported

```text
lambda [-1.499984369453656607...]
RAW_Y5    [0.11 +/- 9.09e-3]
GAUGED_Y5 [0.11 +/- 9.09e-3]
IDENTITY_CHECK [+/- 8.46e-3]
```

Thus the algebra is sound, but applying it only after aggregating coarse
interval moments does not reduce dependency width.  A terminal version must
apply the gauge before summation (or use the paired double-integral form),
and must include the complete annulus and tail with explicit envelopes.

## Full-plane budget sweep (useful but inadmissible)

As a scouting calculation, the seventh-order symbolic monomials were
integrated over the complete quadrant before forming the determinant, and the
order-five companion charge was applied to all 158 born `t` boxes.  Every row
had positive nominal-plus-companion margin; the worst was approximately
`6073.2297` at index 156.  This explains why preserving the cancellation is
promising.

That sweep is **not a certificate**: the companion lemma in
`SURFACE-BESSEL-INTEGRAL-REMAINDER.md` is a half-line statement requiring
`z >= 20`, whereas the full quadrant includes the low-`z` region.  The
calculation therefore applies a valid high-`z` error bound outside its
registered domain.  The script was intentionally removed rather than
archived as evidence.  A real closure must split the low-`z` region and carry
its exact Bessel enclosure into the same cancellation-preserving determinant.

## Required next certificate

For each registered `(delta,t)` box, a future production transcript must
record the exact rational gauge, the signed cell/paired-cell partition, all
four gauged moment intervals, the annulus/outer-tail envelopes, and a replay
that checks the ungauged and gauged determinants intersect.  Any cell whose
envelope is below its declared `z_0` threshold must be moved to the exact
low-`z` lane.  A positive result from the current aggregate wrapper is not
admissible evidence for K2.

This note records a useful structural reduction and a failed coarse
implementation only; all terminal gates remain unchanged.
