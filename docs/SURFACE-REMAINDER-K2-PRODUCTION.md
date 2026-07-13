# K2 positive-lane production contract

**Registered:** 2026-07-12, before any exhaustive positive-lane run  
**State:** `REGULAR_006_CERTIFIED`; `44_POSITIVE_DELTA_BIRTHS_OPEN`;
`EARLIER_EXTENSIONS_QUARANTINED`; `G2_OPEN`

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

The point-overlap test passes, and an origin-touching regression exposed and
fixed one implementation defect in the design module: the second derivative
sum had evaluated the mathematically absent term `0*x^-1`, producing an Arb
indeterminate value.  With the correct lower summation index, all Hessian
coefficients are finite.  The resulting architecture is nevertheless
terminally negative.  On the adversarial lane
`delta in [0,0.004]`, `t in [3.14,pi]`, the constant `KD` enclosure contracts
from `+/-51.4` at grid 8 and `+/-5.38` at grid 16 to the strictly positive
`3.0 +/- 0.334` at grid 32, but the assembled third normalized coefficient is
still `+/-4.74e4`.  Bounding the four moment Hessians separately loses the
determinant cancellation before quotient assembly.  The centred-moment route
is retired; any successor must preserve that cancellation before spatial
absolute values are taken.

The next isolated regular probe uses an orthogonal improvement already paid
for by the exact extraction.  The six-term moment series contains one output
coefficient that the sealed judge deliberately discarded.  The new judge
retains coefficients through order four, subtracts the exact
`r4(c)*delta^3` head, and charges the fourth Taylor coefficient together with
the existing order-four Bessel-companion and moving-band value errors.  The
candidate lane is fixed as `[0,1/200]`, first on the final born `t` box, and
the pre-observation grid ladder is

```text
192, 384, 768, 1024, 1536, 2048.
```

It stops at the first strict outward-positive margin.  A successful stress
result is design evidence only; all 158 born `t` boxes, a production map,
fresh provenance, and an executable joint validator remain mandatory before
the certified `[0,1/250]` boundary can move.

The fixed adversarial probe passes at its first attempted grid, 192.  On
`delta in [0,1/200]`, `t in [3.14,pi]`, it encloses
`abs(r3+r4*delta)` by `1.16125`, the fourth nominal coefficient by
`34306.23`, and the value-error coefficient by `414.03`; the final strict
margin lower endpoint is `1.34903`.  This is not coverage.  Before examining
any other born `t` box, the exhaustive design ladder is fixed as

```text
24, 48, 96, 192, 384.
```

Every one of the 158 immutable born boxes starts at 24 and stops only on a
strict outward-positive lower margin.  Failure at 384 retires this candidate;
a green design run must still be repeated by a provenance-bearing production
driver and checked by an executable coverage validator.

The exhaustive design run is green on all 158 born `t` boxes.  Its first-pass
histogram is `96:151, 192:7`; grids 24 and 48 close no box and grid 384 is not
needed.  A separate sequential tail check fixes the exact boundary: indices
`0--150` use grid 96 and `151--157` use grid 192.  The production run is split
at that boundary into half-open segments `[0,151)` and `[151,158)`.  Both
segments must come from one commit, and the joint validator requires every
index exactly once, the immutable adjacent born partition, the frozen grid,
matching dependency hashes, and 158 strict lower margins.

Both exact-`r4` production segments were executed from commit `4228a6a0` and
pass: 151 rows at grid 96 and seven rows at grid 192.  The joint executable
validator confirms one common commit, the exact segment partition, all 158
adjacent born `t` boxes, the frozen grid map, dependency hashes, and strict
positivity.  The global worst lower margin is
`0.0219753793600584...` at index 150.  Three current run manifests own the
two numerical transcripts and the validator transcript, and the repository
manifest audit accepts all 29 records.  Therefore the regular certificate is
promoted to `[0,1/200] x [0,pi]`: positive delta birth `j=4` is absorbed, and
the remaining positive workload is the 45 births `j=5,...,49`.  G2 remains
open.

That promotion is quarantined by the subsequent outer-domain audit.  Both
the older `[0,1/250]` driver and the exact-`r4` `[0,1/200]` driver enlarged
the nominal core lane but reused `annulus_derivative_bounds()` with its
literal internal `dmax=0.001` and called
`moving_band_value_coefficients()` at its default endpoint domain.  For the
larger lanes the physical transition band begins well below scaled radius 31,
so the recorded value charge omits an annular portion.  The six affected
manifests are quarantined and neither extension carries theorem load.  The
current regular range returns to `[0,1/1000]`; all 49 positive births remain
open.  See `INC-K2-REGULAR-EXTENSION-OUTER-DOMAIN.md` for the repair contract.

The repair is pre-registered before measurement in a byte-separate v2 helper.
Every public v2 entry point requires an exact rational `delta_max`; values
above `1/200` fail.  The annulus uses that cap, the moving-band majorants use
the same lane, and their conservative lower radius is computed as
`floor(1/sqrt(delta_max))` (31 at the sealed endpoint, 14 at `1/200`).  The
first regression must reproduce or enlarge every endpoint outer bound.  Only
after that regression passes may the corrected final `t` box be tried on the
fixed grid ladder `96,192,384,768`.  A stress pass is design evidence only.

The first corrected stress ladder is terminally negative: all four grids
leave the quotient perturbation unresolved.  The cause is isolated in the
coefficientwise moving-band charge, whose largest moment coefficient reaches
about `9.54e51` at `delta_max=1/200`; the annulus is not the source.  The band
was explicitly designated value-only, so the next fixed variant does not
differentiate it.  It bounds the actual zeroth majorant on the complete
exterior of `rho=1/sqrt(delta)`, divides by `delta^5`, and proves by the same
gamma-tail derivative test that the quotient is maximal at `delta_max`.
Before a new stress result is observed, the four direct coefficients at
`1/200` are required to be finite and below their coefficientwise analogues,
with common radius 14 and maximum below 3500.  The spatial grid ladder remains
unchanged.

The direct-band stress remains negative but finite on the full ladder:
its margin contracts from about `-5.17` at grid 96 to `-1.88` at grid 768.
The remaining dominant loss is now identified in the generic quotient
perturbation: it replaces all four moment errors by their maximum, thereby
charging the `HDF` coefficient (about 3461) also to `KD`, `KF`, and `HDD`.
The next fixed judge expands
`Delta(KD*HDF-KF*HDD)` componentwise, uses each emitted moment magnitude and
each separate error coefficient, and lets only the actual `KD` error perturb
the inverse square.  Its regression requires the resulting synthetic stress
constant to be finite and below 20000.  The outer band, delta domain, and grid
ladder are unchanged.

The corrected componentwise stress passes at grid 192.  Grid 96 has strict
lower margin about `-0.21876`; grid 192 has `C_value<=973.884` and strict
lower margin `1.30459`.  Before any other born box is observed, the exhaustive
v2 design ladder is fixed as `96,192,384`.  Every one of the 158 immutable
`t` boxes starts at 96 and stops only at a strict outward-positive margin.
Failure at 384 retires the repaired `1/200` candidate.  A green design cover
still carries no theorem load until rerun by fresh production drivers whose
dependency list includes the v2 outer helper.

The corrected exhaustive design cover is green on all 158 boxes.  Its
first-pass histogram is `96:150, 192:8`; grid 384 is not needed.  A separate
sequential boundary check confirms indices `0--149` at grid 96 and
`150--157` at grid 192.  The production split is therefore fixed as
`[0,150)` and `[150,158)`.  Both segments must be executed from one commit;
the new validator additionally requires `band_radius=14` on every row as
well as the usual hashes, exact rational endpoints, adjacency, frozen grid,
unique coverage, and strict lower margins.

Both corrected production segments pass from commit `c7c7dd76`: 150 rows at
grid 96 and eight rows at grid 192.  Every row records moving-band radius 14.
The joint executable validator confirms one common commit, all dependency
hashes including the v2 outer helper, exact segment boundaries, all 158
adjacent born boxes, the frozen grid map, radius 14, and strict positivity.
The global worst lower margin is `0.0269577269908384...` at index 149.  Three
new current manifests own the two transcripts and validation record; the six
unparameterized predecessors remain quarantined.  Therefore the repaired
regular certificate validly promotes `[0,1/200] x [0,pi]`, absorbs positive
birth `j=4`, and leaves 45 positive births `j=5,...,49`.  G2 remains open.

The next birth is isolated in a byte-separate v3 wrapper so the manifested v2
hashes remain immutable.  Its exact domain ends at `delta_max=3/500`; it
reuses the proved v2 algebra under that cap without changing v2's on-disk or
runtime contract, bypasses v2 caches during the enlarged annulus call, and
requires the direct band radius 12.  Before measurement, the final born
`t` box is fixed on grid ladder `96,192,384`.  The regression requires v2 to
continue rejecting `3/500` after every v3 call.  A stress pass is design only.

The integer-radius v3 stress is terminally negative: the band coefficient is
about `2.77e7` and grid-384 margin about `-2371`.  The true band begins at
`sqrt(500/3)=12.9099...`; rounding all the way down to 12 loses almost one
radial unit inside an exponential tail.  The next geometry-only repair is
fixed at decimal rational radius `129/10`, still strictly below the true
start.  The annulus, direct value majorant, componentwise perturbation, delta
domain, and grid ladder remain unchanged.

The sharp-radius rerun remains terminally negative.  Radius `12.9` contracts
the band coefficient from about `2.77e7` to `4.06e5`, but grid 384 still has
margin about `-2111`.  The dominant term is no longer the band: the nominal
fourth coefficient is about `5.86e7`, versus about `3.55e4` on the certified
`1/200` adversarial box.  Thus the zero-based exact-`r4` interval architecture
has reached its dependency boundary before `3/500`.  No larger grid or finer
band radius is authorized on this route.  The next regular architecture must
subtract the exact `r5(c)*delta^4` head and control a fifth coefficient with a
higher-order Bessel/outer remainder; the alternative is the already registered
positive-birth driver on `[0.005,0.006]`.

Before choosing between those routes, one source diagnostic is frozen at the
final born `t` box and grid 96.  It assembles the fourth normalized coefficient
from the `[0,12]^2` nominal core first, then from the same moments after adding
the v3 annulus/tail.  It cannot certify or retire a range; it only decides
whether delta subdivision must target the core, the outer completion, or both.

That diagnostic gives core `Y4<=1.28e5` but completed `Y4>=7.37e7`; the
annulus is the dependency source.  The next probe fixes the delta partition
to the six immutable births `[j/1000,(j+1)/1000]`, `j=0,...,5`, and grid 96.
For each subbox it recomputes both the nominal core and annulus derivative
series, then takes the maximum fourth coefficient, minimum KD, and separate
moment maxima.  The direct moving-band value error remains one global
`delta_max=3/500` charge at rational radius 12.9.  No result may merge or
delete a subbox, and a stress pass still requires a full t-cover.

The six-box split contracts `max_Y4` to about `3.70e4`, but the global band
from physical coordinate 1 to 1.2 still gives `C_value≈1.27e5` and margin
about `-3.71`.  Since every registered trigonometric/root bound is valid up
to physical coordinate `6/5`, the next exact decomposition moves the
artificial differentiated boundary to `11/10` and leaves only the rim
`[11/10,6/5]` as value error.  At `delta_max=3/500` its pre-registered
decimal lower radius is `71/5=14.2`.  The six delta boxes, grid 96, global
domain, and componentwise perturbation remain unchanged.

The physical-1.1 stress passes at grid 96 with `max_Y4<=36954`,
`C_value<=148.38`, and strict lower margin about `0.8770`.  Before any other
`t` box is observed, the exhaustive derivative cover is fixed to the two
delta boxes `[0,1/200]` and `[1/200,3/500]`, physical split `11/10`, and grid
ladder `96,192,384`.  This coarser derivative cover is still a superset lemma;
any production validator must enumerate the six absorbed thousandth births
separately.  A design pass cannot promote the certified `1/200` boundary.

The first exhaustive attempt with those same two boxes in the annulus fails
at `t in [0,0.02]`: a wide annulus cell cannot resolve its root even at grid
384.  The repaired cover keeps the two expensive core integrations but fixes
the annulus partition to all six thousandth births.  Each narrow annulus box
is combined with the core enclosure of its containing coarse box.  This is a
valid superset bound, preserves two core grids per `t` box, and prevents a
coarse annulus interval from entering the root.  The physical split and grid
ladder remain unchanged.

The repaired exhaustive design cover is green on all 158 `t` boxes.  Its
histogram is `96:137, 192:21`; grid 384 is unused, and the worst lower margin
is `0.0303077645991...` at index 136.  The production map is fixed as indices
`0--136` at grid 96 and `137--157` at grid 192, split into `[0,137)` and
`[137,158)`.  The validator must require the two core boxes, six annulus
births, physical split `11/10`, band radius `71/5`, all 158 adjacent t boxes,
one commit, dependency hashes, frozen grids, and strict margins.

Both `3/500` production segments pass from commit `1d22b6ba`: 137 rows at
grid 96 and 21 rows at grid 192.  Their joint validator confirms the two core
boxes, six annulus births, physical split `11/10`, radius `71/5`, all 158
adjacent `t` boxes, one commit, dependency hashes, frozen grids, and strict
positivity.  The global worst lower margin is `0.0303077645991296...` at
index 136.  Three current manifests own the transcripts and validation; the
repository audit accepts 35 manifests.  Therefore the regular certificate is
promoted to `[0,3/500] x [0,pi]`, absorbs positive birth `j=5`, and leaves the
44 births `j=6,...,49`.  G2 remains open.

The next byte-separate v4 probe is pre-registered through `delta=7/1000`:
core boxes `[0,3/500]`, `[3/500,7/1000]`, seven thousandth annulus births,
physical split `11/10`, rational band radius `131/10`, and adversarial grid
ladder `96,192,384`.  v3 must continue rejecting `7/1000` after every call.
