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
`t=0.05,1.5,3.13` show the same contraction pattern.  This was the first
viable design; the Bessel and spatial charges added below were not hidden in
those numbers.

The first omitted charge is now bounded without differentiating a bound.
The true A/B companions differ from their nominal order-four polynomials by
at most explicit moment constants times `delta^5`; the largest constant is
less than `3.710`.  Direct perturbation of the bilinear quotient therefore
costs `C_Bessel delta^4`.  With the deliberately coarse box bounds
`KD>=2`, `|moment|<=10`, the executable global formula gives
`C_Bessel<1000`, hence less than `0.001` after division by the endpoint
`delta^2` budget at `delta=1/1000`.  Production uses the sharper KD and
moment bounds emitted by each series box.  At that stage the
spatial/moving-boundary derivative tail was the remaining endpoint charge;
the next paragraph records its implementation.

The spatial charge now has an executable polynomial--Gaussian envelope.
Normalized delta derivatives are propagated as majorants
`C rho^p exp(-a rho^2)` with the exact rate
`a=2 c_min (1-sin(0.6)^2) sinc(0.6)^2/4`.  A single uniform-t annulus
cover handles `12<=max(sigma,tau)<=32`; outside radius 32, the elementary
upper-incomplete-gamma bound integrates every majorant.  The last moving
physical band is not differentiated: its missing coefficients and its
fifth-order integral remainder are charged directly as
`e_band delta^5`, with `e_band<4.87`.  Thus no moving-boundary term is
silently omitted.

After adding the annulus, radial tail, moving-band value perturbation, and
Bessel perturbation before quotient assembly, the two adversarial endpoint
t-boxes pass at grid 96.  On `[0,0.02]`, `Y3_abs<=472.669`; on the final
born box `[3.14,pi]`, `Y3_abs<=2135.917`, combined value coefficient
`C_value<=471.910`, and normalized margin remains approximately `0.10`.
The exhaustive 158-box design cover is still required before this lane can
be promoted; all output remains labelled `DESIGN_COVER_PASS` meanwhile.

That exhaustive cover has now been rerun as the authoritative certificate.
All 158 born t boxes pass on `[0,1/1000]`; five boxes use grid 192, every row
prints the outward-rounded lower endpoint of its margin, and the final box
has `margin_lower>=0.1024088458`.  The transcript is owned by
`surface-remainder-k2-endpoint-20260712T125718Z.json` and its validator
checks adjacency, refined count, all positive lower margins, six dependency
hashes, and every executed commit blob.  This promotes only the K2 endpoint
lane.  The 49 positive delta boxes and G2 remain open under the separately
pre-registered `384 delta^4` target.

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

For the 49 positive born delta boxes, the regular scaled series cannot use a
single `[0,1/20]` parameter ball: its nominal `Y3` radius reaches
`4.0e13`.  A fixed-physical-square series removes that dependency.  It uses
`h=delta/(2R)`, the exact phase `(2R-4c)/delta`, and the convergent A/B
companions, while keeping `[0,6/5]^2` fixed.  Direct cell intervals remain
too wide (`Y3` radius `7.7e7` at grid 96 on the last delta box).  Propagating
spatial gradients and Hessians for all six delta coefficients, integrating
the linear phase exactly, and refining by the terminal Jacobian gives the
following design ladder at `t=2.9`, `delta in [0.049,0.05]`:

```text
uniform 24       Y3 radius 1.83e7
uniform 48       Y3 radius 1.15e7
adaptive 4096    Y3 radius 1.04e7
adaptive 16384   Y3 radius 9.78e6
```

The literal cubic weight of this last box requires roughly `Y3<5e6` before
earlier-box charges are counted.  Both adaptive rungs are therefore rejected;
the flattening from 4,096 to 16,384 leaves rules out further cell growth with
the same integrands.  The next architecture applies the exact series
calibration `KF-q KD`, `HDF-q HDD` inside each spatial cell before integration;
the bilinear is algebraically invariant.  No positive delta box is promoted
by these design numbers.

An exact fourth head coefficient now changes the positive-box target.  The
independent symbolic/Gaussian engine extended through one additional order
gives

```text
r4(c) = (28c^8+41c^6-1464c^4+1856c^2-500)/(1024c^12)
```

as the coefficient of `delta^3` in `Y`, while reproducing `T,r2,r3` exactly
in the same run.  On `c in [1/sqrt(2),1]`, its endpoint values are
`551/128` and `-39/1024`; at `delta=1/20` its worst direct contribution is
below `5.4e-4`.  The still-open analytic load is therefore a uniform
`delta^4` remainder, for which a coefficient of order 300 would already fit
the smallest registered slack.  This identity is exact head data, not by
itself a remainder certificate or a G2 promotion.

The manifested next symbolic order gives the coefficient of `delta^4`:

```text
r5(c) = (12940c^10+16077c^8+173288c^6-1300912c^4
         +1358400c^2-346112)/(262144c^15).
```

Its endpoint values are `494883 sqrt(2)/32768` and `-86319/262144`.
After charging `r4 delta^3+r5 delta^4`, a 2,000-box Arb budget sweep
leaves coefficient greater than `7676.5` for an order-`delta^5` remainder;
the integer target `7600` is pre-registered before any such remainder run.
This is again exact head plus a budget contract, not the missing bound.

The coefficientwise exact-series engine next reproduces that `r5` formula
before deriving and matching

```text
r6(c) = (8148c^12+17095c^10+10768c^8+634576c^6-2557408c^4
          +2283296c^2-549376)/(131072c^18),
```

the coefficient of `delta^5`.  The executed transcript, dependency hash,
and exact target match are owned by run manifest
`surface-remainder-delta0-sixth-head-20260712T143105Z`.  Its endpoint values
are `1074449/8192` at `c=1/sqrt(2)` and `-152901/131072` at `c=1`.
Charging `r4,r5,r6` in the same 2,000-box Arb sweep leaves coefficient
greater than `153507.7` for a delta-six remainder; `150000 delta^6` was
registered before a remainder run.  This remains head data, not G2.

Two absolute-majorant architectures for the remaining order-six moment tail
are rejected.  Collapsing all spatial degrees before Gaussian integration
produces `1e57--1e64`.  Preserving every degree until the final radial gamma
integral improves this to

```text
KD 3.43e18,  KF 6.95e20,  HDD 7.83e18,  HDF 1.67e21,
```

still far outside the `7600 delta^5` quotient budget.  The loss is therefore
not spatial degree bookkeeping but taking absolute values before the exact
bilinear cancellation.  The next admissible remainder engine must retain
signed Gaussian polynomials through bilinear formation and series division,
then majorize only the final integral remainder.  Enlarging these rejected
momentwise constants is not a completion path.

A second attempted shortcut is also rejected.  Refining the same physical
cells against the value coefficient `Y0` rather than `Y3`, and subtracting
the exact head only after forming the interval value on the whole last born
delta box, gives at `t=2.9`

```text
delta [0.049,0.05],   4096 leaves: residual abs upper 1.9013
delta [0.0495,0.05],  4096 leaves: residual abs upper 0.92375
delta [0.0495,0.05], 16384 leaves: residual abs upper 0.85143
registered last-box budget:                    0.0022587
```

Thus value-directed refinement alone misses by more than two orders of
magnitude and has the same spatial plateau.  The active correction is not a
larger tree: choose a point centre for each delta box, propagate a formal
perturbation, subtract `T+r2 delta+...+r6 delta^5` coefficientwise, and only
then evaluate the retained residual series on the centred perturbation ball.
The executable now supports this ordering.  It remains design work until the
Taylor truncation, companion error, and physical outer band are charged in a
terminal positive-box judge.

The cubic-spatial implementation advances that correction: it integrates the
complete quadratic Taylor polynomial against the affine phase and charges
only total-degree-three spatial derivatives.  At the last half-box and
`t=2.9`, uniform grids 8, 16, 32, 64 contract the nominal head-subtracted
radius as `7.72, 0.464, 0.0413, 0.00479`; a 4,096-leaf sensitivity-adaptive
tree reaches `0.00218`.  These are design values before the order-six Bessel
companion error and delta-Taylor truncation charge.  They establish genuine
contraction but do not yet pass the registered total budget.

The terminal successor retains the spatial Taylor polynomial through degree
four, charges total degree five, and uses separate centre/whole-box `t` jets
through order four.  A first hybrid centre/box jet was rejected before
promotion; the repaired algebra assembles both tracks separately.  On the
born descendant `delta in [0.0495,0.05]`, `t in [2.9,2.92]`, the complete
terminal accounting is

```text
nominal t-Taylor enclosure   0.000838217262286
delta-six Taylor tail       0.000000031174144
order-six Bessel charge     0.000050375193229
total                       0.000888623629659
budget                      0.002206594100159
margin                      0.001317970470500
```

`KD` has certified lower bound `1.93939885225`.  The manifested run uses
1,024 centre cells plus two 64-cell auxiliary tracks and is validated by
`validate_surface_remainder_positive_stress_transcript.py`.  This is the first
terminal positive K2 box.  G2 remains open pending the exhaustive born cover;
the fixed production ladder and the preregistered uniform-sixth-coefficient
shortcut are recorded in `SURFACE-REMAINDER-K2-PRODUCTION.md`.

The sealed regular architecture has subsequently been extended and rerun in
production on `[0,1/250]`.  Two transcripts cover index segments `[0,136)` and
`[136,158)` from the same commit; their joint executable validator checks all
158 born `t` boxes, exact rational endpoints, adjacency, the fixed grid map,
dependency hashes, and strictly positive outward lower margins.  The worst
lower margin is `0.000519408406216...` at index 44.  This promotes the regular
lane through three positive delta births.  G2 remains open on the 46 births
from `delta=0.004` through `0.05`.

The exact fourth head now yields a stronger manifested successor.  Retaining
the fourth normalized Taylor coefficient, subtracting `r4(c)*delta^3`, and
charging the existing order-four Bessel and moving-band value errors closes
`[0,1/200] x [0,pi]`.  Two production transcripts from commit `4228a6a0`
cover `[0,151)` at grid 96 and `[151,158)` at grid 192; their joint validator
checks all 158 born boxes and finds worst strict lower margin
`0.0219753793600584...` at index 150.  The new certificate absorbs positive
delta birth `j=4`.  G2 remains open on the 45 births from `delta=0.005`
through `0.05`.

The later outer-domain audit quarantines both claimed regular extensions.
Their nominal series and printed margins reproduce, but the outer annulus was
still evaluated only through `delta=0.001` and the moving-band value charge
started at the endpoint radius 31.  The safe current regular claim is again
`[0,1/1000] x [0,pi]`; all 49 positive births remain open.  The independent
fixed-physical-domain stress descendant is unaffected.

The byte-separate v2 repair now restores the extension without reviving any
quarantined transcript.  It makes `delta_max` mandatory in the annulus and
moving-band majorants, uses radius 14 at `1/200`, bounds the band directly at
value level, and perturbs the determinant componentwise.  Fresh production
segments from commit `c7c7dd76` cover all 158 born `t` boxes at grids 96 and
192.  Their joint validator finds worst strict lower margin
`0.0269577269908384...` at index 149.  The current safe regular range is thus
again `[0,1/200] x [0,pi]`; 45 positive births remain open.

The same repaired architecture now extends one further birth.  It evaluates
the core on `[0,1/200]` and `[1/200,3/500]`, subdivides the annulus into all
six thousandth births, differentiates through physical coordinate `11/10`,
and charges only the rim to `6/5` at radius `71/5`.  Fresh production from
commit `1d22b6ba` covers all 158 `t` boxes; the validator reports worst lower
margin `0.0303077645991296...` at index 136.  The current regular range is
`[0,3/500] x [0,pi]`; 44 positive births remain open.
