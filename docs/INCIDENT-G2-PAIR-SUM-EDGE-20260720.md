# Incident: paired Wronskian is numerically stable only after a new tail contract

**Date:** 2026-07-20  
**Scope:** G2 scaled bulk, moving-edge diagnostics  
**State:** `DESIGN-ONLY`

The high-order Taylor enclosure used for the scaled bulk becomes sign
indefinite at the moving edge near `beta=101.8`, `lambda=2.8`, even though a
500-digit independent computation gives a negative Wronskian.  This is an
enclosure failure, not evidence of a sign change.

The exact pair identity gives a better numerical representation.  With
`J_m=exp(-beta) I_m(beta)`, `A_m=exp(-4 beta) a_m`, and
`B_m=exp(-4 beta) b_m`,

```text
W_scaled = sum_{m<n} (A_m B_n-A_n B_m) T_mn(t).
```

At `t=pi-lambda/beta`, parity gives
`T_mn(pi-x)=(-1)^(n-m+1) T_mn(x)`.  The probe
`scripts/probe_surface_scaled_pair_sum.py`, run at 800 Arb bits with 240
modes, returns

```text
beta=101.8, lambda=2.8:
W_scaled_truncated = -7.46902634791555...e-108 +/- 4.2e-247.
```

The probe now also applies an explicit pointwise tail bound.  It uses
`J_(n+1)/J_n <= beta/(2(n+1))`, polynomial envelopes for the `A_m` tail, and
`|T_mn| <= 2(m+n)`.  At the same point the certified enclosure remains
strictly negative and the tail upper bound is below `9.4e-396`.

The independent regression
`scripts/validate_surface_scaled_pair_sum_tail.py` checks the same envelope
against a 40-mode extension at four points (`beta=20,50,101.8`) at 1000 Arb
bits; all four comparisons pass.

The pair-central-Taylor prototype is retained separately in
`scripts/probe_surface_scaled_pair_taylor.py`.  A full mixed-derivative call
was too slow for an interactive run even at order `(12,17)`; it is therefore
not presented as production evidence.  The missing optimization is to group
the pair derivatives by `p=n-m` before interval evaluation.

## Exact minor factorisation replay (2026-07-20)

The direct minor can be rewritten without changing the mathematics.  With
`B_m=m J_m^4`, `r_m=J_{m+1}/J_m`, and
`u_m=r_m+2m/beta` from the exact Bessel recurrence,

```text
A_m B_n - A_n B_m = B_m B_n (R_m-R_n),
R_m=((m-1)u_m^2+(m+1)r_m^2)/m.
```

This form is implemented as `pair_sum_ratio` in
`scripts/probe_surface_scaled_pair_sum.py`.  The independent regression
`scripts/validate_surface_scaled_pair_ratio_identity.py` reproduces the
direct pair sum at the three registered stress points (`beta=20,50,101.8`)
with overlapping Arb balls.  It materially reduces pointwise cancellation,
but a beta/lambda interval still widens to the wrong sign; no G2/G6
promotion follows.  The remaining admissible work is a grouped central
Taylor or a proved monotonicity enclosure on a frozen box cover.

This is a genuine point certificate, but not a uniform theorem certificate:
direct interval boxes lose the sign through dependency before the pair sum is
formed.  The finite-box tail inequalities still need a monotonicity proof
for the beta interval and a grouped `(delta,lambda)` cover.  Therefore this
route does **not** promote G2, G6, or the manuscript.  The next admissible
step is the uniform box version of this pair-sum tail contract.

## Mean-value beta repair (candidate only)

The next repair keeps the pair grouping and replaces a wide two-parameter interval
evaluation by a beta mean-value enclosure: a midpoint Taylor polynomial, a whole-cell
beta-derivative bound, the explicit mode tail (and its derivative), and independent
lambda/beta Taylor remainders.  The frozen driver is
`scripts/certify_surface_scaled_pair_mean_value_cell.py`; the exact-rational cover audit
is `scripts/audit_surface_scaled_pair_mean_value_cover.py`.

One cell is currently certified as a candidate:

```text
beta  = [1629/16, 3259/32] = [101.8125,101.84375]
lambda= [3/2,151/100]      = [1.5,1.51]
M=115, beta/lambda order=50, Arb=500 bits
total_upper = -5.9884206602134...e-109
```

The same driver also passes the exploratory wider band `lambda in [1.5,1.6]`
with `total_upper` about `-5.86e-109`; that output is not yet a manifested production
unit.  The cover manifest records only the one-cell result and is checked with exact
rational tiling, byte-identical replay, dependency hashes, and strict negativity.
This remains `CELL_CERTIFIED_CANDIDATE` with promotion `NONE`: it supplies no load on
G2 or G6 until a pre-registered finite cover, a tail/precision budget, and an
independent production/replay campaign are complete.

An exploratory width test on the same beta cell with `lambda=[3/2,23/10]`
(`lambda` width `0.8`) terminated at the driver's registered failure
`mean-value upper endpoint is not negative`.  It produced no certificate and is
not included in the positive manifest; the result only bounds the useful width
of this first-order campaign unit.
