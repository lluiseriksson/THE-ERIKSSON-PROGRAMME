# K2 positive-lane production contract

**Registered:** 2026-07-12, before any exhaustive positive-lane run  
**State:** `REGULAR_004_CERTIFIED`; `46_POSITIVE_DELTA_BIRTHS_OPEN`; `G2_OPEN`

This record specializes the immutable born partition in
`SURFACE-REMAINDER-K2-PARTITION.md` to the repaired terminal integrator.  It
does not alter the `150000 delta^6` target in
`SURFACE-REMAINDER-R7-PREREG.md`.

## Per-box accounting

Every terminal positive box must add, before comparison with the budget,

1. the centre residual after coefficientwise subtraction of
   `T+r2 delta+...+r6 delta^5`, evaluated only through retained delta
   degrees zero through five;
2. the first three ordinary `t` derivatives at the centre, with Taylor
   weights `h`, `h^2/2`, and `h^3/6`;
3. `h^4/24` times a whole-box fourth-`t`-derivative enclosure;
4. the sixth delta-Taylor coefficient, not included in item 1, evaluated with
   the constant delta parameter ranging over the complete delta box;
5. the order-six Bessel-companion perturbation, using `KD>0` and moment
   magnitudes after undoing the exact `KF-q KD`, `HDF-q HDD` calibration.

The spatial Taylor polynomial is retained through total degree four and
integrated exactly against the affine phase.  Only total-degree-five spatial
derivatives are charged by absolute values.  All quantities are outward-rounded
Arb balls.

## Deterministic spatial refinement ladder

Each born box starts on uniform grid 8.  If the terminal margin is not
strictly positive it advances, without inspecting any alternative mesh, through

```text
8 -> 16 -> 24 -> 32.
```

The centre track alone advances on this ladder.  The whole-`t`-box and
whole-`(delta,t)` auxiliary tracks start on grid 8 and advance through the same
ladder only if their individual enclosures are non-finite or the combined
margin fails after the centre reaches grid 32.  A failure at grid 32 triggers
the already permitted bisection of that parameter box; it does not permit a
larger threshold, a widened box, or a different unregistered spatial mesh.

Every uniform grid is split into four contiguous row slices with one common
calibration.  The parent process reconstructs outward endpoint hulls and sums
the four pieces.  A grid-8 smoke reproduced the sequential five-derivative
enclosure exactly at printed precision.

## Uniform sixth-coefficient shortcut

The same registered inequality admits a stronger coefficient-level proof.
After the exact head through degree five has been removed, Taylor's theorem
gives

```text
|R(delta,t)| <= C6(t) delta^6.
```

Accordingly, before any exhaustive result is observed, the production driver
may first try to prove on each born `t` box that the nominal whole-parameter
sixth coefficient plus the order-six Bessel coefficient is strictly below
`150000`.  A coefficient bound proved on a delta superset is a common analytic
lemma applied separately to every contained birth; it is not a merged terminal
box, and the final coverage table must still list every delta birth.

The fixed delta-superset ladder is

```text
[1/1000,1/20]
    -> [0.001,0.002], [0.002,0.004], [0.004,0.008],
       [0.008,0.016], [0.016,0.032], [0.032,0.050].
```

The full interval is attempted first.  If it fails, all six listed macroboxes
are used; no data-dependent macro boundary is allowed.  If one macrobox fails
at spatial grid 32, its constituent born delta boxes revert to the per-box
accounting above.  The endpoint `[0,1/1000]` remains owned by the independent
regular certificate and is never inferred from this shortcut.

The first macro design sweep is rejected because the interval sum does not
resolve the constant `KD` coefficient even at grid 32.  Before reverting to
all births, one analytic intersection is allowed and fixed here.  In the proof
of Lemma `lem:mass`, the true main-square `KD` contribution dominates `T1`,
while `T1 >= m_low >= 1/2` because the remaining displayed mass terms are
subtracted nonnegative upper bounds.  The order-six nominal companion differs
from true main `KD` by at most

```text
e_KD delta^7,   e_KD <= 9.071080589,
```

so throughout the positive lane its constant coefficient may be intersected
with

```text
KD_nominal >= 1/2 - e_KD*(1/20)^7 > 0.4999999929.
```

The Bessel correction is mandatory; intersecting directly with `1/2` is
forbidden.  Only coefficient zero is restricted.  Higher delta coefficients
and all final remainder intervals remain the raw outward-rounded sums.

The post-floor macro sweep exposed one further representation loss: forming
`delta^4*KD^2` first and inverting the product can reintroduce zero through
interval multiplication.  The coefficient lane therefore uses the exact
factorization already used by the terminal jet driver: invert the primitive
series `delta` and `KD` separately, then multiply `delta_inv^4*KD_inv^2`.
Both primitive constants are strictly positive.  A point regression requires
coefficientwise overlap with the original quotient assembly.

The complete six-macro design sweep after both repairs is a terminal negative
result for this shortcut.  Every macro fails through grid 32.  At the most
favourable macro `[0.032,0.05]` the nominal sixth-coefficient majorant remains
about `4.11e22`; at `[0.001,0.002]` it is about `3.30e86`, against the fixed
budget `150000`.  The robust factorization resolves the denominator and prints
finite coefficients, so this is no longer an inversion artifact.  The
coefficient shortcut is retired and all positive births revert to the per-box
Taylor accounting.  Its fixed macros and failures remain documented to prevent
the same absolute-coefficient route from being repeated with larger grids.

## Promotion boundary

The stress-box terminal run may certify only its one born descendant.  G2 can
move only after an exhaustive transcript proves adjacency and coverage of all
49 positive delta births and all ordered `t` births, every row has a strictly
positive terminal margin, the endpoint certificate remains valid, and an
executable validator checks the union and provenance.

## First terminal result

The last half of the last delta birth at the registered stress `t` birth,

```text
delta in [0.0495,0.05],   t in [2.9,2.92],
```

passes with total `0.000888623629659`, budget `0.00220659410016`, and
strict margin `0.00131797047050`.  The run separately reports 1,024 centre
cells, 64 whole-`t` cells, 64 whole-`(delta,t)` cells, `KD>1.9393`, delta-tail
charge `3.12e-8`, and companion charge `5.04e-5`.  Transcript and dependencies
are owned by manifest
`surface-remainder-positive-stress-20260712T182652Z`; the executable transcript
validator checks hashes, counts, positivity, margin, verdict, and one-box
scope.  This result validates the terminal accounting but does not imply any
unrun birth.

## Higher-spatial-order design ruling

An isolated total-degree-seven driver was tested on the full last delta birth
and the interior `t` birth `[1,1.02]`.  At grid 8 its complete nominal
enclosure is about `0.099996`, versus `1.663742` for degree five: a real
factor-`16.6` improvement, but still roughly `48` times the total budget.
The measured per-cell cost is about `2.8` times larger.  Advancing degree seven
to grid 16 would therefore cost approximately the same as the passing
degree-five `8->16->24` ladder, without changing coverage complexity.  Degree
seven is retained as a checked negative design result, not promoted to the
production lane.  The next improvement must preserve cancellation across the
assembled bilinear before spatial absolute values are taken.

The next design identity is fixed before measurement.  Instead of one common
calibration, choose point series `qK=KF/KD` and `qH=HDF/HDD`, and integrate

```text
KF'  = KF  - qK KD,
HDF' = HDF - qH HDD.
```

Then the numerator is recovered exactly as

```text
KD HDF' - KF' HDD + (qH-qK) KD HDD.
```

Both subtracted moments are centred inside every spatial cell before the
degree-five remainder is majorized.  Omitting the correction term or choosing
`qK,qH` after a box result is forbidden.

The grid-8 measurement of that identity is terminally negative as a design
route: on the full last delta birth and `t in [1,1.02]` it gives total
`1.6657459` against budget `0.0020762`, essentially the original degree-five
width.  The correction term restores the dependency loss together with the
exact determinant, so separate moment calibrations are retired.

The next isolated smoke fixes a different exact regrouping before observing
its result.  If `x,y` denote two points of the physical square and
`K,H,D,F` the four primitive factors, the ordered pair plus its transpose is

```text
(D_x F_y-F_x D_y) (K_x H_y D_y-K_y H_x D_x).
```

Consequently the determinant is the half integral of this antisymmetrized
kernel over the square product.  The first smoke groups the already rigorous
degree-five cell integrals by unordered cell pairs.  It can diagnose interval
dependency but cannot promote a box: promotion would require enclosing the
antisymmetrized kernel itself before spatial absolute values, then repeating
the centre, whole-`t`, and whole-parameter tracks and the registered companion
accounting.

The cell-integral regrouping smoke is negative: at grid 8 its value enclosure
is `1.8243027`, compared with `1.6398070` when the same 64 cells are accumulated
as four moments first.  Thus algebraic pair ordering after each two-dimensional
cell has already been enclosed does not recover dependency.  This variant is
retired.  Only a genuine four-variable jet of the displayed pointwise kernel,
formed before the spatial Taylor remainder is majorized, can test the direct
determinant route.

The genuine four-variable degree-five smoke is also terminally negative as a
design architecture.  Already on the minimal `2 x 2` spatial grid for each
copy its head-subtracted residual enclosure is `1.6213816e7`.  Even the ideal
fifth-order contraction under repeated uniform halving would require spatial
grids in the hundreds for each copy, hence billions of cell pairs.  The direct
kernel identity remains valid, but this 4D interval-Taylor realization is
retired before any larger mesh is attempted.

The sealed regular endpoint architecture is now the active extension probe.
It proves the final `Theta3` inequality directly and therefore need not satisfy
the stronger auxiliary `150000 delta^6` accounting used by the positive lane.
The authoritative `[0,1/1000]` scripts and manifest inputs remain byte-invariant;
an isolated driver tests larger zero-based lanes.  The last `t` birth passes on
`[0,0.002]` at grid 192 with margin about `0.58`, while `[0,0.005]` is unresolved
through grid 192.  The fixed next probes are `[0,0.003]` and `[0,0.004]`, after
which any successful candidate must be checked across all 158 born `t` boxes
and receive a new manifest and coverage validator before it can replace any
positive birth.

The fixed ladder resolved that boundary.  On the final adversarial `t` birth,
`[0,0.003]` passes at grid 384 with margin about `0.50`, and `[0,0.004]`
passes at grid 1024 with margin about `0.12`; `[0,0.005]` fails at grid 1024
with margin about `-1.44` and is retired.  The exhaustive design cover for
`[0,0.004]` is pre-registered with the immutable grid ladder
`96,192,384,768,1024`.  It runs every one of the 158 original `t` births,
advances a row only after a failed strict margin, and cannot print
`CERTIFIED`.  A green design cover must be rerun under a separate provenance
driver and validator before the first three positive delta births are removed
from the remaining positive-lane workload.

The first exhaustive design ladder closes indices `0--154` but exhausts grid
1024 on born box 155, `t in [3.10,3.12]`, with a zero-crossing margin.  Before
any larger result is observed, the spatial ladder is extended by exactly
`1536,2048` for the unresolved tail.  The driver now prints and tests the
outward lower endpoint explicitly; low-relative-accuracy Arb display strings
such as `[+/- r]` are never interpreted by eye as positivity.  Boxes already
closed retain their first passing grid and need not be rerun during this design
continuation; production still requires a single validated coverage record.

The extended design cover is green on all 158 born `t` boxes.  Its first-pass
grid histogram is `192:45, 384:91, 768:16, 1024:4, 1536:2`; grid 2048 is not
needed.  This fixes the production map, in index order, as

```text
0--44:192, 45--135:384, 136--151:768,
152--154:1024, 155--156:1536, 157:1024.
```

The production driver is split only for runtime into half-open index segments
`[0,136)` and `[136,158)`.  Both print the same commit and dependency hashes,
exact rational `t` endpoints, the fixed grid, and the outward margin lower
endpoint.  A joint validator requires one common commit, the exact two segment
ranges, every index exactly once, adjacency of the born boxes, the frozen grid
map, and 158 strictly positive lower margins before any G2 promotion.

Both production segments and the joint validator now pass from commit
`755a13eb`.  The joint record has 158 unique adjacent born `t` boxes and worst
strict lower margin `0.000519408406216...` at index 44.  Three manifests own
the two numerical transcripts and the validator transcript.  Therefore the
regular certificate is promoted from `[0,1/1000]` to `[0,1/250]`; it absorbs
positive delta births 1, 2, and 3.  The remaining positive workload is the 46
born delta boxes `[j/1000,(j+1)/1000]`, `j=4,...,49`.  This is a real G2
advance, not G2 closure.

The next design route attacks the dominant cost of the regular certificate,
not its already certified claim.  The existing regular integrator treats each
spatial cell as a constant interval and needed grids through 1536.  A new
isolated series-valued spatial dual evaluates the midpoint, cancels the two
linear spatial terms exactly on the symmetric cell, and charges only the
whole-cell Hessian.  The `sinc^2` entire series carries explicit tails for
every retained delta coefficient and both spatial derivatives.  It must first
overlap the sealed point integrand coefficientwise; only then may grid
contraction be measured.  This design module cannot alter the manifested
`[0,1/250]` evidence.
