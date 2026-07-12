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

The first coefficient is now exact as well.  Expanding the regularized
geometry and the convergent Bessel companions through order one, then
integrating every monomial with exact two-dimensional Gaussian moments, gives

```text
Y(0,t) = (4c^2-1)/(8c^3) = T(c)
```

by symbolic simplification, after separately asserting the leading bilinear
zero.  This reproduces the pre-registered closed form independently of the
older extraction engine.  The remaining K2 analytic obligation is the
`r2(c)` coefficient and a uniform second-order remainder through the
localized completion.

The same independent engine has now been extended through order two.  It
includes the quadratic entire-geometry terms, the quadratic common phase,
and the first three relative coefficients of both scaled Bessel factors.
Exact Gaussian integration and quotient algebra give

```text
Y_delta(0,t) = (-8c^4+15c^2-4)/(32c^6) = r2(c)
```

by symbolic simplification.  Thus both pre-registered head coefficients are
now reproduced on the regular lane.  K2 is not yet closed: the remaining
load-bearing item is the uniform `O(delta^2)` enclosure, including the
completion, strong enough for the `Theta3(c)` budget.

One further exact order has also been extracted on the same lane.  Carrying
the cubic entire-geometry, phase, and Bessel terms gives the coefficient of
`delta^2` in `Y` as

```text
r3(c)=(-12c^6-485c^4+796c^2-224)/(1024c^9),
```

again by exact symbolic simplification.  This independently reproduces all
three closed forms `T`, `r2`, and `r3` used by the judge.  It does not replace
the required inequality: the tail beyond this exact head and the completion
must still fit the registered `Theta3` budget uniformly.

The first fixed-core natural-interval pilot rejects `[0,1/20]` as one delta
box: after seven spatial refinements the outer annulus still cannot resolve
the common root because the same wide delta interval appears in every
factor.  The regular endpoint carrier itself remains valid.  The born
endpoint interval `[0,1/100]` is the active finiteness pilot; `(1/100,1/20]`
must be covered by explicit delta subdivision (and the exact complement),
not by one dependency-heavy interval.

The endpoint cancellation now has a viable ball-series architecture.  The
regular nominal carrier is differentiated in `delta` with Arb series, and the
exact full-plane identity `B(0)=0` is used in its integral form for
`B(delta)/delta`; no interval containing zero is divided.  On the registered
endpoint lane `[0,1/1000]` at `t=2.9`, a grid-96 design run bounds the
normalized third derivative coefficient of `Y` by `1610`, while the exact
`Theta3-|r3|` slack permits approximately `1969`.  Point probes at
`t=0.05,1.5,3.13` show the same contraction pattern.  This is not a K2
certificate: the current series driver intentionally omits the fifth-order
Bessel companion error and the derivative form of the analytic outer tail,
and it has not run the born ordered t cover.  Those two charges must be added
before the endpoint lane can enter the direct judge.

On `[0,1/100]` the raw fixed-grid core ladder is finite but not competitive:
the `KD` radius contracts only `7.39 -> 4.35 -> 3.34` on grids
`8 -> 16 -> 32` (the other three moments show the same slowing).  Further
uniform gridding is rejected.  The next integration implementation must use
a spatial centered form for the regular carrier, then add the exact
complement; these raw boxes carry no judge load.

The regular phase now has certified spatial gradients and Hessians, with
entire-series derivative tails checked against independent multiprecision
derivatives.  Exact integration of its cellwise linear part materially changes
the grid-32 core boxes:

```text
KD                 [0 +/- 3.34]  ->  [3 +/- 0.490]
KF/delta           [0 +/- 3.88]  ->  [-2 +/- 0.833]
HDD/delta^2        [0 +/- 1.13]  ->  [0.9 +/- 0.0741]
HDF/delta^3        [0 +/- 1.31]  ->  [0 +/- 0.956]
```

This is still design evidence on `[0,1/100]`.  It identifies the next
specific task: center the non-exponential prefactors (especially HDF), then
attach the fixed-domain complement before forming a bilinear judge.

The prefactors are now centered without differentiating the Bessel remainder:
each is split as `R(1/z)*G`, the convergent companion encloses `R` on the
whole cell, and only the elementary geometry `G` is expanded affinely with a
Hessian remainder.  At grid 32 the core boxes sharpen to

```text
KD                  [2.6 +/- 0.0872]
KF/delta            [-2 +/- 0.318]
HDD/delta^2         [0.9 +/- 0.0702]
HDF/delta^3         [-0.7 +/- 0.0805]
```

All four now have the expected sign on the endpoint core.  This still is not
a `Y` enclosure: the exact complement must be added moment by moment before
the bilinear cancellation is assembled.

The Gaussian endpoint calibration is now applied inside every spatial cell,
before integration.  The exact identity
`B=KD*GN-KN*HDD` is preserved.  On the grid-32 endpoint core it yields

```text
KN = [0 +/- 0.192],   GN = [0 +/- 0.0797],
B_core = [0 +/- 0.363].
```

This is a real reduction from the uncentered core bilinear radius `0.483`,
but it is not yet near a terminal `Y` budget and still omits the complement.
No additional uniform mesh is promoted; the next load-bearing step remains
the regular fixed-domain completion and a joint partition in delta.

The same centered machinery now integrates `(1-chi)` on the fixed endpoint
square `[0,12]^2`, which lies inside every scaled physical square for
`delta<=1/100`.  At grid 16 its calibrated moment radii are

```text
KD 1.23e-4,  KN 8.33e-4,  HDD/delta^2 4.27e-5,  GN 2.95e-4,
completion-only bilinear radius 6.56e-8.
```

This shows the transition completion is numerically tame under rigorous
balls.  It is not the whole complement for `delta<1/100`: the moving physical
square extends beyond 12.  A uniform analytic tail outside `[0,12]^2` and the
core--completion cross terms remain mandatory before the endpoint interval
can enter the direct judge.

The moving-square tail beyond `[0,12]^2` is now bounded analytically.  The
elementary inequalities `sin(x)/x >= sin(0.6)/0.6` and
`pq/c^2 <= sin^2(0.6)(p+q)` give the uniform phase rate

```text
phase <= -0.2132 (sigma^2+tau^2).
```

Combining the resulting Gaussian strip moments with explicit polynomial
bounds for `D` and `F/delta` gives absolute four-quadrant tail bounds

```text
KD 9.89e-14,  KN 1.90e-11,  HDD/delta^2 5.81e-14,  GN 1.12e-11.
```

Thus the endpoint value-level complement (fixed square plus outer tail) is
accounted for.  Promotion still requires the delta-remainder enclosure and
core--complement cross-term assembly in the joint judge.

A quadtree weighted by the exact first-order bilinear sensitivities reduces
the endpoint-core bilinear radius from `0.363` (uniform grid 32) to `0.205`
at 1,023 leaves and `0.176` at 4,095 leaves.  The contraction is real but
already flattening: the shared delta interval, not spatial resolution, is now
dominant.  Further cell growth is rejected.  The production architecture must
separate the analytic endpoint box from a born ordered partition of
`(0,1/100]` before spending more spatial work.

Shrinking the endpoint box to `[0,1/1000]` at the same 4,095-leaf budget
reduces the core bilinear radius from `0.176` to `0.0207`, close to linear in
the delta width.  This confirms that delta subdivision is the right axis,
but also shows that plain interval division by delta would retain an unusably
large constant.  The exact `T+r2*delta+r3*delta^2` head must be subtracted in
the regular integrand/Taylor model before the endpoint box can be sealed.

At the minimum-budget bulk edge `(t,beta)=(0.6,20)`, the 65,536-cell
physical-square judge failed with margin `-0.00132402`; the next quadtree
level, 262,144 cells, passed with residual upper `0.00113777`, budget
`0.00269140`, and margin `+0.00155363`.  A binary longest-axis variant at
65,536 leaves was both slower (`704 s` versus `441 s`) and wider (margin
`-0.00152511`), so it is rejected and not retained in the production code.
