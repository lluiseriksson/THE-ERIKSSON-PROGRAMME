# Direct joint-remainder route — current status

**Date:** 2026-07-12

**Gate:** G2 remains `OPEN_DESIGN`

The first post-registration Arb point run completed at the registered
stress location `t=2.9`, with the candidate threshold `beta=20`:

```text
effective cells     65,536
Y                   [0.39 +/- 4.09e-3]
absolute residual   <= 0.00501633856846
Theta3/beta^2       >= 0.00716017174363
certified margin    >= 0.00214383317516
verdict              DESIGN_POINT_PASS
```

The transcript is owned by
`s2-direct-point-20260712T073531Z.json`.  It proves the inequality at one
point only.  It does not cover a beta interval, a t interval, or the analytic
`delta=0` endpoint, so it carries no theorem load.
The exact executed dependency is preserved as
`scripts/archive/surface_remainder_y_integrator_3593648d.py`; later
development of the live integrator cannot rewrite the run's provenance.

## Parameter-width and coordinate pilots

The natural-interval parameter pilot is rejected.  At 16,384 spatial cells,
even `(Delta beta,Delta t)=(0.001,0.0001)` widened `Y` to `+/-0.646`, far
outside the budget.  The code now has a loud forced-subdivision depth floor;
the earlier unbounded recursion on a non-finite box is no longer possible.

Exact automatic t-jets were then checked against independent multiprecision
differentiation in both Bessel lanes.  For a t-box of width `0.001`, the
Taylor contributions at the stress point are sized by

```text
|Y_t| radius contribution       <= 3.7e-5
|Y_tt/2| radius^2 contribution  <= 1.5e-6
```

so the parameter-Taylor route survives.  A second attempted improvement,
Gaussian extraction on the fixed scaled square
`[0,(6/5)sqrt(20)]^2`, is rejected: the value radius contracted only
`2.48 -> 2.13 -> 1.97` on the `1024 -> 4096 -> 16384` ladder.  This is not
a certificate architecture.

The active next step is therefore a bivariate parameter Taylor cover whose
central values use the physical-square integrator, with derivative bounds on
smaller boxes.  A point mesh increase or a natural parameter interval alone
is not a G2 completion strategy.

## Convergent Bessel source now closed

The Bessel-value part of the analytic route no longer relies on the
nondecreasing absolute coefficient fold.  The positive integral
representations of `A=exp(-z)I_1(z)/z` and
`B=exp(-z)I_2(z)/z^2` now give uniform fifth-order relative companions on
`z>=20`, with outward-rounded constants

```text
C_A <= 0.635,   C_B <= 2.427,   C_ratio <= 3.181.
```

Exact quotient algebra yields

```text
r(z)=B/A
 = 1/z - 3/(2z^2) + 3/(8z^3) + 3/(8z^4)
   + 63/(128z^5) + error,
|error| <= 3.181/z^6.
```

On `z=z_s sqrt(1-w)`, `0<=w<=1/2`, its explicit deficit has remainder
at most `28.622/z_s^6`.  The proof, executable arithmetic, and tests are in
`SURFACE-BESSEL-INTEGRAL-REMAINDER.md` and
`surface_bessel_integral_remainder.py`.

This closes one named source only.  The common exponential, trigonometric
geometry, spatial completion, analytic `delta=0` patch, and uniform
integration remain; therefore `(H_tail)` and G2 stay `OPEN_DESIGN`.

The removable geometry at `delta=0` is now factored exactly in
`surface_remainder_delta0_geometry.py`.  With
`P=sin^2(sigma sqrt(delta)/2)/delta` and the analogous `Q`, both evaluated
by a convergent entire `sinc^2` series,

```text
phase = -4 c (w/delta)/(1+sqrt(1-w)),
1/z   = delta/(4 c sqrt(1-w)),
```

and `F/delta` has an explicit polynomial factorization.  Arb boxes crossing
`delta=0` contain independent positive-delta evaluations and the exact
Gaussian endpoint.  This resolves the geometry-level `0/0`; K2 still needs
the regular Bessel prefactors, moment integration, bilinear cancellation,
and the terminal joint inequality on a nonzero delta interval.

The first of those four items is now implemented pointwise.  Factoring the
scaled Jacobian and the common exponential gives finite enclosures for

```text
KD,   KF/delta,   HDD/delta^2,   HDF/delta^3
```

on boxes crossing `delta=0`.  The fifth-order Bessel companions are evaluated
directly in `h=1/z`, so `h=0` is a polynomial endpoint rather than an
attempt to construct `z=infinity`.  The new pointwise carrier contains
independent positive-delta evaluations and stays finite at zero.  Moment
integration and the extra bilinear zero needed by `Y` are still open.

The full-plane endpoint integral is now exact.  Gaussian moments give

```text
(KF/delta)/KD = (HDF/delta^3)/(HDD/delta^2)
              = -(2C+1)/(2c),
```

so the leading normalized bilinear numerator vanishes identically.  This is
an executable symbolic contract at multiple `t` values, not a small floating
residual.  What remains for K2 is the first and second delta coefficient with
uniform integral remainders, including the localized completion.

At the minimum-budget bulk edge `(t,beta)=(0.6,20)`, the 65,536-cell
physical-square judge failed with margin `-0.00132402`; the next quadtree
level, 262,144 cells, passed with residual upper `0.00113777`, budget
`0.00269140`, and margin `+0.00155363`.  A binary longest-axis variant at
65,536 leaves was both slower (`704 s` versus `441 s`) and wider (margin
`-0.00152511`), so it is rejected and not retained in the production code.
