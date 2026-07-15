# Five-family right-edge tail: moving charts and a fixed exterior gap

## Exact angular partition

Let `eta=delta*c`, where every occurrence in the divided-difference
integrals satisfies `|c|<=lambda/2`; hence
`|eta|<=3/500`.  The two U-family phases have the exact forms

```text
sin u + cos(u+eta)
 = 2 sin(pi/4-eta/2) cos(u-[pi/4-eta/2]),

sin u - cos(u+eta)
 = 2 cos(pi/4-eta/2) cos(u-[3pi/4-eta/2]).
```

The two denominator phases, after writing the circle variable as `u=2a`,
are the same formulas centered at `a=-pi/4-eta/2` and
`a=pi/4-eta/2`.  Thus both problems use identical moving charts.

Take the central angular intervals

```text
[pi/8,3pi/8], [5pi/8,7pi/8]
```

for U and their translates by `-pi/2` for the denominator.  The central
integration `|q|<=4`, with angular displacement `sqrt(delta) q`, stays
strictly inside these intervals for `delta<=1/125`.  On the whole central
angular partition both positive Bessel arguments are at least `3/4`, so
`1/z<=delta/(3/4)<1/20`; the already proved integral-form Bessel companion
is valid there, including at `delta=0`.

## Near tail

Relative to the common factor `exp(2 sqrt(2)/delta)`, the exact phase is

```text
2(A(eta)-sqrt(2))/delta
 - A(eta) q^2 sinc(sqrt(delta)q/2)^2.
```

On the central angular intervals,

```text
A(eta) sinc(...)^2 > 4/3,
|2(A(eta)-sqrt(2))/delta| <= lambda <= 3/2.
```

Therefore each of the four chart/sided tails is bounded by

```text
exp(3/2) integral_4^infinity exp(-4q^2/3)dq
 <= exp(3/2-64/3)/(2(4/3)4).
```

The normalized Bessel derivative factors are bounded without
differentiating any asymptotic remainder: every `z` derivative is reduced
exactly to `I0,I1`, and the integral-form companions enclose those two
values.  The design evaluator gives near-tail charges below `6.5e-11` for
each of `U0,U1,U2,B0,B1`.

## Far angular exterior

On the complement of the two central intervals,

```text
sin u+|cos u| <= 131/100.
```

The shift costs at most `3/500`, so the shifted phase is at most
`329/250`.  The rational inequality `sqrt(2)>707/500` gives the doubled
phase gap

```text
2(707/500-329/250)=49/250.
```

For integer order, the Bessel integral representation gives
`|D_z^k I_n(z)|<=exp(|z|)`.  Faà di Bruno is evaluated as a finite positive
jet majorant, and all five scaled families have the same worst polynomial
prefactor `delta^(-3/2)`.  Since

```text
delta^(-3/2) exp[-49/(250 delta)]
```

is increasing up to `delta=1/125`, its endpoint bounds the half-open face
and gives far-exterior charges below `3.3e-8` for every family.  The far
majorant deliberately charges angular length `pi`; the actual exterior
length is `pi/2`, so this is a documented conservative factor two.

The current total design budgets are:

```text
U0 < 3.207e-8, U1 < 2.164e-8, U2 < 8.896e-9,
B0 < 3.220e-8, B1 < 2.190e-8.
```

## Finite bridge beginning at beta 20

For the prospective overlap `20<=beta<=125`, take the narrower moving
charts `|q|<=5/2` and central angular half-width `7/50`.  The maximum
angular shift is `3/80`.  Exact rational checks and outward-rounded
elementary inequalities give

```text
v >= 201/1000,       central Gaussian rate >= 4/3,
exterior phase <= 117/100,   sqrt(2) > 707/500,
doubled exterior gap = 2(707/500-117/100) = 61/125.
```

The integral-form companions are used down to `z=4`; no asymptotic
remainder is differentiated.  At the deliberately uniform endpoint
`delta=1/20`, the combined near- and far-tail design charges are

```text
U0 < 0.005804, U1 < 0.004262, U2 < 0.002151,
B0 < 0.006770, B1 < 0.005300.
```

The finite composition jet is evaluated with this lane's actual
`DELTA_MAX`, not the half-line value `1/125`.  An initial design probe
incorrectly reused the latter constant in the far derivative chains; its
five smaller totals were discarded before any parameter result was
promoted.  The regression test now requires the finite order-five chain
constant to dominate the half-line one.

These bounds pass their geometry and finiteness test, but they are not by
themselves a parameter certificate.  In particular, one `delta` box of
width `1/1000` at the finite endpoint, on the coarse central grid and with
the uniform charges added independently, loses the lower sign of `P0`.
This is a recorded enclosure-width failure, not a negative value of the
target.  The finite lane must therefore use a refined central grid,
beta-dependent tail charges, a continuation of the compact certificate, or
a combination of these; it may not promote the coarse box.

A separate compact-lane design moved the normalized/regular splice from
`1/500` to `1/1000`.  It covered `[20.6,21]` in 40 adjacent beta boxes and
continued, with adaptive subdivisions, through beta
`22.620686340332032`.  The next box again collapsed at the splice near
`d=0.000999`; subdivisions below `10^-6` did not recover it.  This is useful
overlap design evidence, not a manifested union: no finite G5 interval is
promoted by this note.

## Status

The moving-saddle identities, angular inequalities, argument floor,
Gaussian rate, and rational exterior gap are machine-audited by
`verify_surface_right_edge_five_family_tail_geometry.py`.  The displayed
half-line and finite-family budgets are still **design output**: production requires a frozen
partition, a dependency ledger, a transcript validator, and an independent
re-run.  No terminal G5 claim is made here.
