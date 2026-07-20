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

The adjacent beta cell
`[3259/32,815/8] x [3/2,19/10]` has now passed with the same frozen configuration
and an independent byte-identical replay (`total_upper` about
`-3.97e-109`).  The two-cell exact-rational union is audited by
`run-manifests/surface-scaled-pair-mean-value-cover-beta101p8125-101p875-lambda150-190-20260720.json`.
This is a finite candidate cover only; it does not alter the G2/G6 board.

A third contiguous unit, `beta=[815/8,3261/32]` with the same lambda band,
also passes (`total_upper` about `-3.67e-109`) and has production plus
byte-identical replay.  The three-cell manifest extends the exact union to
`beta=3261/32=101.90625`; it remains candidate evidence and carries no gate
promotion.

## First cell in the former beta gap

The archived scaled-bulk candidates end at `beta=100.0625`.  The adjacent
cell `beta=[100.0625,100.09375]`, `lambda=[1.5,1.9]`, with the frozen
`M=115`, order-50/50, 500-bit mean-value driver, now has production and
byte-identical replay; its strict upper endpoint is about `-2.72e-107`.
The twice-as-wide cell `[100.0625,100.125]` fails the registered mean-value
inequality, so the dyadic width `1/32` is retained for this local unit.  The
manifest is candidate-only and does not close the remaining beta gap or alter
G2/G6.

The next four dyadic cells were then run by the bounded campaign launcher,
with two workers and fixed orders/precision.  All four production/replay pairs
passed, extending the exact-rational candidate union to
`beta=[100.0625,100.21875]`.  The five-cell manifest records this union and
keeps `promotion=NONE`; it is still not the full `[100.0625,1000/9]` splice
and therefore cannot change G2.

An eight-cell continuation, generated by the exact-rational campaign launcher,
passed all production/replay pairs and covers `beta=[100.21875,100.46875]`
at the same lambda band.  Its independent union manifest passes the
no-gap/no-overlap audit.  This remains candidate evidence: the remaining beta
interval to `1000/9`, the scaled-tail splice, and the global G2 judge are open.

An exploratory width test on the same beta cell with `lambda=[3/2,23/10]`
(`lambda` width `0.8`) terminated at the driver's registered failure
`mean-value upper endpoint is not negative`.  It produced no certificate and is
not included in the positive manifest; the result only bounds the useful width
of this first-order campaign unit.

## Second eight-cell continuation

The next exact-rational campaign covered eight adjacent beta cells,
`beta=[3215/32,3223/32]=[100.46875,100.71875]`, with the same
`lambda=[3/2,19/10]`, `M=115`, orders `(50,50)`, and 500 Arb bits.  All eight
production runs and their independent replays passed with `failures=0`.
The manifest
`run-manifests/surface-scaled-pair-mean-value-cover-beta100p46875-100p71875-lambda150-190-20260720.json`
records the eight transcript/replay hashes.  The exact-rational cover audit
reports `SCALED PAIR MEAN-VALUE COVER AUDIT PASS` and verifies a Cartesian
tiling with no gaps or overlaps.

This is still `CELL_CERTIFIED_CANDIDATE` with `promotion=NONE`.  It does not
promote G2 or G6: the beta interval above remains only one finite segment of
the unresolved splice, and the global tail, overlap, and analytic monotonicity
obligations are unchanged.

## Third eight-cell continuation

The following exact-rational campaign covered eight more adjacent beta cells,
`beta=[3223/32,3231/32]=[100.71875,100.96875]`, with
`lambda=[3/2,19/10]`, `M=115`, orders `(50,50)`, and 500 Arb bits.  All eight
production runs and independent replays passed (`failures=0`).  The manifest
`run-manifests/surface-scaled-pair-mean-value-cover-beta100p71875-100p96875-lambda150-190-20260720.json`
records the hashes, and the exact-rational cover audit verifies the Cartesian
tiling with no gaps or overlaps.

The status remains `CELL_CERTIFIED_CANDIDATE` with `promotion=NONE`; this
finite segment does not close the remaining splice or promote G2/G6.

## Fourth eight-cell continuation

An additional exact-rational campaign covered
`beta=[3231/32,3239/32]=[100.96875,101.21875]`, again with
`lambda=[3/2,19/10]`, `M=115`, orders `(50,50)`, and 500 Arb bits.  All eight
production/replay pairs passed (`failures=0`).  The manifest
`run-manifests/surface-scaled-pair-mean-value-cover-beta100p96875-101p21875-lambda150-190-20260720.json`
and its cover audit record the exact tiling and byte-identical hashes.

This remains candidate evidence only (`promotion=NONE`); neither G2 nor G6
is promoted by this finite continuation.

## Fifth eight-cell continuation and provenance repair

The next campaign covered `beta=[3239/32,3247/32]=[101.21875,101.46875]`
with `lambda=[3/2,19/10]`, `M=115`, orders `(50,50)`, and 500 Arb bits.  The
launcher reported 8/8 numerical passes.  Two cells initially differed only in
their recorded `git_head`, because the K4 preregistration commit landed between
their production and replay.  Both affected cells were regenerated in
production and replay under the same frozen HEAD; the corrected hashes are
the ones recorded by the candidate manifest.  No stale transcript is
promoted, and G2/G6 remain unchanged.

## Sixth eight-cell continuation

The next exact-rational campaign covered
`beta=[3247/32,3255/32]=[101.46875,101.71875]`, with the same
`lambda=[3/2,19/10]`, `M=115`, orders `(50,50)`, and 500 Arb bits.  All eight
production/replay pairs passed (`failures=0`); the cover audit verifies the
Cartesian tiling and byte-identical hashes.  This leaves only the short
candidate interval `[3255/32,1629/16]` before the topology audit's next gap.
The manifest is candidate-only and does not alter G2/G6.

## Boundary three-cell continuation

Three final dyadic cells cover
`beta=[3255/32,1629/16]=[101.71875,101.8125]` with the fixed lambda band
and frozen numerical configuration.  Production and replay pass for all
three cells and the exact cover audit passes.  This reaches the endpoint of
the currently manifested paired component; the remaining topology gap begins
at `1629/16` and extends to `1000/9`.  The manifest remains candidate-only.
