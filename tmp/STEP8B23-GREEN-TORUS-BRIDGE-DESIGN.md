# Step 8b.23 — mass-uniform Green torus bridge (scratch design)

Status: static design only.  This file is not evidence, is not imported by
`YangMillsCore`, and must not be promoted before Step 8b.22 has a terminal
cold verdict.

## Exact target

Construct a continuous function on `UnitAddTorus (Fin 4)` whose sample at
the finite reciprocal point `ell / N'` is the literal CMP89 stabilized Green
endpoint at

```
cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  = fun mu => -2*pi*(ell mu).val/N'
```

and whose `n`-th `UnitAddTorus.mFourierCoeff` is the source-normalized CMP89
Green value at the **positive** physical displacement

```
(u + M*n) / M.
```

This coefficient orientation is forced by Mathlib's definition

```
mFourierCoeff f n = integral (mFourier (-n) * f).
```

With the torus parameterization `p(t) = -2*pi*t`, using the centered
fundamental cube `t in [-1/2,1/2]`, the Fourier character and the Green phase
combine as

```
exp(-2*pi*i*n.t) * exp(-2*pi*i*t.(u/M))
  = exp(i*p(t).(n + u/M)).
```

There is no `fourierNeg` and no negative coefficient displacement in this
column-oriented bridge.  The already sealed transpose route retains its own
separate Fourier-negation transport.

## Brick ladder

### G23.1 — mass-uniform Green holomorphy/continuity

Copy the logical shape of
`differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius`,
but replace the old mass-positive common-denominator input by
`cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform`.
The result must be valid at `mass = 0` on the complete polydisc.  Derive real
continuity as a theorem; do not accept continuity as a parameter.

### G23.2 — mass-uniform physical face seam

The existing Green theorem
`cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalPeriodShift_of_nonzero`
is cold-sealed at source checkpoint
`ce2522edfb26366dee93db84640dcff6298f141c` (ledger Addendum 833), but it
accepts a **unit-lattice** endpoint displacement.  That is not the endpoint
used by the normalized fine Green: at Step 8b.23 the displacement is
`u/(L^j)`, and replacing it by `u` would silently lose the scale.

The exact fine-scale cancellation already exists for the differentiated
endpoint in
`cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFinePeriodShift_of_nonzero`:
a centered-alias wrap contributes `2*pi*L^j`, which pairs with `u/(L^j)` to
give the integer phase `2*pi*u`.  G23.2 must reproduce that construction for
the Green numerator without its derivative factor: fine-lattice bare Green
momentum factor, displayed momentum term, complete alias reindexing, then
transfer back to the stabilized extension.  It must not instantiate the old
unit-lattice Green theorem.

Therefore the old global-period route remains open, but it is no longer the
preferred route.  Mathlib's `AddCircle.liftIoc_continuous` needs only
continuity on a closed fundamental interval and equality of its two faces.
The already sealed
`cmp89Eq251FineSymbol_ne_zero_of_boundaryFace` is mass-uniform; the only old
positive-mass dependency in `cmp89Eq251DisplayedDomain_of_boundaryFace` is
the stabilized-denominator floor.  Replacing it with
`cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform` therefore
produces the literal Green face seam at `mass = 0` without a density or
removable-point argument.

Static candidate for G23.1 and the mass-uniform face seam:
`tmp/BalabanCMP89Eq248GreenMassUniformHolomorphy.draft.lean`.  It replaces
only the old positivity-based common-denominator producer by the already
cold-sealed mass-uniform floor and now contains the explicit fine-lattice
Green alias-cycle construction described above.  Its final seam composes the
mass-uniform boundary domain with that fine-scale rational-domain period.  It
asserts no global period.

Acceptance gate: the public seam has no assumption `unitSymbol != 0`, no `if`
value at the seam, no supplied periodic family and no replacement of
`u/(L^j)` by a unit displacement.  The value must remain the literal
stabilized Green endpoint.

### G23.3 — closed-cube quotient construction

Do not require a global periodic raw function.  Use the compact source

```
X = (mu : Fin 4) -> Set.Icc (-(1/2) : Real) (1/2)
```

and the coordinate quotient map

```
q : X -> UnitAddTorus (Fin 4)
q x mu = (x mu : UnitAddCircle)
```

The centered cube is forced by the domain on which G23.2 is proved. Under
`p(t) = -2*pi*t`, its two faces are `p = pi` and `p = -pi`, exactly the
mass-uniform seam. The earlier candidate `Icc 0 1` would instead require an
unproved seam between `p = 0` and `p = -2*pi`, passing through the removable
mass-zero central singularity. It is rejected.

The map is continuous and surjective (choose coordinate representatives with
`AddCircle.equivIoc`).  Since `X` is compact and the torus is Hausdorff,
`Topology.IsQuotientMap.of_surjective_continuous` supplies the quotient map.
Descend the continuous cube function with `Topology.IsQuotientMap.lift`.

The factors-through proof must replace coordinates one at a time.  Equality
of two representatives in `Icc (-1/2) (1/2)` means either literal equality or the two
opposite endpoints; the latter case consumes the named G23.2 face seam.  No
global period, representative choice or a.e. equality is accepted.  Isolate
this topology as a generic finite-product lemma before specializing the
physical Green endpoint.

The generic lemma must derive, rather than assume,
`Function.FactorsThrough f q`.  Its finite proof is fixed as follows.

1. For `x y : Icc (-1/2) (1/2)`, prove from equality of their images in
   `UnitAddCircle` the trichotomy

   ```
   x = y  or
     (x = -1/2 and y = 1/2)  or
     (x = 1/2 and y = -1/2).
   ```

   Split only on whether each value equals `1/2`. In the non-endpoint branch,
   both representatives lie in `Ico (-1/2) (1/2)`, so consume
   `AddCircle.coe_eq_coe_iff_of_mem_Ico`.  In the endpoint branches use the
   literal `AddCircle.coe_period` equality.  Do not introduce a general
   integer-modulo witness.
2. For two cube representatives `x,y`, define the intermediate cube
   `replace S` which uses `y i` on a finite set `S` of coordinates and `x i`
   elsewhere.  Induct over `Finset.univ`.  At the inserted coordinate, the
   trichotomy from item 1 gives either reflexivity or exactly one orientation
   of the named face seam; all other coordinates are definitionally fixed.
3. The resulting equality `f x = f y` is the required fibre proof passed to
   `Topology.IsQuotientMap.lift`.  A public theorem accepting an arbitrary
   `Function.FactorsThrough` value is not an acceptable physical endpoint:
   it would merely rename G23.2.

Pinned signatures inspected for this route:

- `Topology.IsQuotientMap.lift` takes a continuous map and a literal
  `Function.FactorsThrough` proof;
- `Topology.IsQuotientMap.lift_comp` returns the exact pullback equality;
- `AddCircle.EndpointIdent` has only the endpoint constructor;
- `AddCircle.homeoIccQuot` realizes the one-coordinate quotient;
- `AddCircle.coe_eq_coe_iff_of_mem_Ico` gives injectivity away from the upper
  face;
- `Topology.IsQuotientMap.of_surjective_continuous` supplies the product-cube
  quotient after continuity and coordinatewise surjectivity are proved.

For integration, use the already available exact measure transport:

```
UnitAddCircle.measurePreserving_mk
MeasureTheory.measurePreserving_pi
```

Thus the Haar integral on the four-torus is the product integral over the
centered unit cube. No new general Fubini theorem is required.

### G23.4 — normalized physical integral dictionary

Change variables `p = -2*pi*t` on
`t in Ioc (-1/2) (1/2)`. Its image is `[-pi,pi)`, while the repository's
literal `cmp89Eq249NormalizedFourDimensionalBrillouinIntegral` uses the
translated parameter `x in (0,2*pi]`, hence `p in (-pi,pi]`. These domains
differ only at their opposite boundary faces. Prove equality by the affine
measure transport plus the named G23.2 seam (or by an explicit null-boundary
integral equality which still cites the seam for the pointwise descended
function). Do not identify the half-open intervals definitionally. The
Jacobian `(2*pi)^4` must cancel the literal source normalization already
present in `cmp89Eq249NormalizedFourDimensionalBrillouinIntegral`.

### G23.5 — coefficient theorem and sample theorem

Prove, as separate named statements:

1. the finite torus sample equals the Step-8b.21 column endpoint integrand;
2. `mFourierCoeff` equals the normalized physical Green at `(u+M*n)/M`;
3. the coefficient family is absolutely summable from the physical
   exponential Green bound;
4. `hasSum_mFourier_series_apply_of_summable` reconstructs every finite-grid
   sample with the same positive character convention used by Step 8b.22.

Only after these four statements are proved may
`cmp99Flat_normalizedFiniteGridFourierSeriesSample_eq_residueClass` be applied.

The sample theorem has one additional discrete gate. Evaluation of the
descended torus function at `ell/N'` uses the centered representative of that
circle point, while Step 8b.21 is stated at the literal uncentered momentum
`-2*pi*ell/N'`. For `ell != 0`, transport the complete stabilized endpoint
between those representatives by the source-specific physical-period
reindexing, deriving its non-singular domain from the centered momentum. For
`ell = 0`, use the already sealed zero-fibre branch and do not cancel the
central symbol. Face seam alone does not prove this interior period transport,
and no global periodicity premise may be introduced.

## Source-specific Green bound needed before G23.5

The coefficient family is the literal
`cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen` at mass zero.  Its
definition already exists, but the current integrability theorem still uses
`mass > 0` and there is no exponential bound for this Green value.  Do not
reuse the differentiated Eq. (2.51) endpoint bound: that object contains the
scaled difference and a unit Holder edge.

The finite ladder is:

1. **Green noncentral quotient.**  Bound
   `bareGreenNumerator / fineSymbol` on the common strip.  Reuse the sealed
   single-amplitude alias strip bound, the noncentral fine-symbol gap and the
   `alpha = -1` radial redistribution already used by
   `BalabanCMP89Eq249ComplexNoncentralAliasQuotientBound`.  The absence of
   the derivative factor must remain visible; this is a new theorem, not a
   specialization of the endpoint theorem.
2. **Green numerator bound.**  Combine the central single-amplitude branch,
   `cmp89Eq251CentralFineSymbolStripUpperBound`, and the finite noncentral
   quotient sum.  Keep the central/noncentral split explicit.
3. **Mass-uniform reciprocal.**  Consume
   `norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform`;
   no `mass > 0` premise survives.
4. **Signed physical phase.**  The Green phase at fine integer displacement
   `u` contributes

   ```
   exp (-rho * xi * cmp89Eq251LatticeL1Length u),
   xi = cmp89Eq249FineLatticeSpacing L j.
   ```

   This is **not** `cmp89SignedLatticeL1ExponentialWeight rho u`: that latter
   form is in unit-lattice coordinates.  Reuse
   `norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour` and
   `cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement`; do not import
   the unit-holder normalization from the differentiated endpoint.  Keep the
   alias-dependent phases inside the finite sum, exactly as the sealed
   `BalabanCMP89Eq251FineLatticePhasedNoncentralSum` does.
5. **Contour telescope and normalized integral.**  Repeat the already sealed
   coordinatewise endpoint contour mechanism with the Green holomorphy and
   mass-uniform face seam from G23.1--G23.2.  The result is the literal
   normalized Green bound

   ```
   norm (cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
     L j 0 a u)
     <= BGreen(a,rho) * exp (-rho * xi * l1(u)).
   ```

6. **Absolute summability.**  Apply the exact full-lattice product theorem in
   `tmp/BalabanCMP89SignedLatticeL1TotalSum.draft.lean`, but do **not** apply
   the full-lattice theorem directly at the fine rate `rho / M`: that would
   introduce a spurious `M^4` in dimension four.  First prove the affine-fibre
   estimate

   ```
   exp (-(rho/M) * |u + M*n|_1)
     <= exp ((rho/M) * |u|_1) * exp (-rho * |n|_1).
   ```

   Then sum only the owner variable `n` at rate `rho`.  This supplies the
   `Summable coefficient` required by Step 8b.22 and by the torus Fourier
   reconstruction with no fine-volume loss.

At the Step-8b.22 specialization `L = M`, `j = 1`, the affine residue class
is `u + M*n` and `xi = M^-1`.  Thus the fine-coordinate exponent is
`-(rho/M) * l1(u + M*n)`, whose asymptotic owner-coordinate rate is `rho`.
Record both units in the theorem names or docstrings; never silently replace
`rho/M` by `rho` before the affine residue transport.

For the centered residue convention in four dimensions,
`|u|_1 <= 4*M/2 = 2*M`.  Hence the only residue prefactor is bounded by
`exp (2*rho)`, uniformly in `M`.  This exact factor must remain visible in the
G23.5 coefficient bound.  It is not to be absorbed into `BGreen`, and it is
not a cardinality factor.

The coordinatewise input for this centering estimate is already sealed as
`two_mul_abs_cmp99SourceFlatQprimeCenteredCoarseAlias_le`.  It may be summed
over `Fin 4` only after the G23.5 sign dictionary proves that its
`cmp99SourceFlatQprimeCenteredCoarseAlias` is the same representative used by
the positive coefficient displacement `u + M*n`.  The theorem represents
`-ell mod M`; importing its numerical bound while ignoring that orientation
would recreate the row/column defect in a new guise.

The Fourier-series equality is still separate: Step 8b.21 identifies the
finite physical fibre with the stabilized endpoint at each coarse momentum,
whereas Step 8b.22 aliases any already identified absolutely summable
coefficient family.  Neither theorem alone proves that the normalized Green
values are the Fourier coefficients of the endpoint function.

## Existing APIs confirmed in the pinned tree

- `UnitAddTorus.mFourierCoeff`
- `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`
- `UnitAddCircle.measurePreserving_mk`
- `MeasureTheory.measurePreserving_pi`
- `Topology.IsOpenQuotientMap.piMap`
- `Topology.IsQuotientMap.lift`
- `Topology.IsQuotientMap.lift_comp`

## Explicit exclusions

- Do not reuse the derivative-endpoint contour bound as a Green bound.
- Do not infer global periodicity from the displayed formula at its zero.
- Do not insert `fourierNeg` into the column coefficient convention.
- Do not treat `[-pi,pi)` and `(-pi,pi]` as the same interval by `rfl`.
- Do not count this bridge, or Step 8b.22 alone, as attaining window 15 or
  discharging a terminal `PreEq136` field.

## Static G23.5 summability sub-brick

Draft file:
`tmp/BalabanCMP89SignedLatticeL1TotalSum.draft.lean`.

The finite-box theorem already sealed in
`BalabanCMP89SignedLatticeL1ExponentialSum` is not sufficient for the torus
Fourier reconstruction: `hasSum_mFourier_series_apply_of_summable` needs a
genuine `Summable` coefficient family.  The static draft therefore isolates
four claims:

1. nonnegativity of the full product weight;
2. `Summable` of the weight on `(Fin d -> Int)` by induction through
   `Fin.consEquiv` and `Summable.mul_of_nonneg`;
3. the exact total mass
   `((1 + exp (-delta)) / (1 - exp (-delta))) ^ d` via
   `Summable.tsum_mul_tsum`;
4. the coarse bound for a fixed affine residue class
   `n |-> u + M*n`, using its injectivity and
   `tsum_comp_le_tsum_of_inj`;
5. the physical-scale affine-fibre bound at rate `rho/M`, transported to the
   exact owner-scale geometric mass at rate `rho`, with no `M^d` loss;
6. the centered-representative prefactor bound `exp (rho*d/2)`, specialized
   downstream to the literal `exp (2*rho)` in dimension four.

Pinned Mathlib source signatures were inspected directly:

- `Summable.mul_of_nonneg`:
  `Mathlib/Analysis/Normed/Ring/InfiniteSum.lean:34`;
- `Fin.consEquiv`:
  `Mathlib/Data/Fin/Tuple/Basic.lean:174`;
- `Summable.tsum_prod` and product reindexing:
  `Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean:255`;
- real `tsum_comp_le_tsum_of_inj`:
  `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:525`.

The residue-class theorems are intentionally algebraic.  They do **not** yet
identify the physical Fourier coefficient displacement with `u + M*n`; that
conversion belongs to the named G23.5 coefficient dictionary.  They do fix
the otherwise dangerous unit conversion: the input rate is literally
`rho/M` in fine coordinates and the summed geometric mass is literally at
rate `rho` in owner coordinates.

## Quotient-measure implementation gate

For topology, use the closed-cube quotient described in G23.3 rather than a
global covering map.  The relevant generic constructors are:

- `Topology.IsQuotientMap.of_surjective_continuous` for a compact source and
  Hausdorff target;
- `Topology.IsQuotientMap.lift` and `lift_comp`;
- `AddCircle.equivIoc` to prove coordinatewise surjectivity;
- `AddCircle.EndpointIdent` / `homeoIccQuot` as the canonical description of
  the only face identification.

For the integral, define the source measure on the centered half-open unit
cube by

```
Measure.pi (fun _ : Fin 4 =>
  volume.restrict (Set.Ioc (-(1/2)) (1/2)))
```

and combine the four statements
`UnitAddCircle.measurePreserving_mk (-(1/2))` with
`MeasureTheory.measurePreserving_pi`.  The target product measure is the
literal `volume` by `MeasureTheory.volume_pi`.

The topological source uses centered `Icc`; the measure source uses centered
`Ioc`. This is intentional, not a definitional identification: `Icc` exposes
both physical `+/-pi` faces for the quotient continuity proof, while `Ioc` is
the fundamental domain in the literal `measurePreserving_mk` theorem. The
descended map composed with the covering map agrees pointwise with the raw
integrand on `Ioc`; only the later comparison with the repository's opposite
half-open Brillouin convention needs a boundary-null transport.

Important API distinction: the covering map is not injective and hence not a
`MeasurableEmbedding`.  Do **not** try to close the integral transport with
`MeasurePreserving.integral_comp`, whose pinned signature requires such an
embedding.  Instead:

1. rewrite the target Haar measure using the `map_eq` field of the product
   `MeasurePreserving` proof;
2. apply `MeasureTheory.integral_map` with the covering map measurable and the
   descended integrand continuous (therefore ae-strongly measurable).

The source signatures were checked at:

- `Mathlib/MeasureTheory/Constructions/Pi.lean:909`;
- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1052` (`integral_map`);
- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1099`
  (`MeasurePreserving.integral_comp`, deliberately excluded here).

This transport reaches the centered unit cube. The subsequent affine
scaling/reflection and opposite-half-open boundary transport to the
repository's literal `cmp89Eq249FourDimensionalBrillouinMeasure` remain a
named G23.4 theorem; they are not definitional reduction.

The exact one-coordinate affine identity is isolated statically in
`tmp/BalabanCMP89CenteredBrillouinAffineSlice.draft.lean`:

```
(2*pi)^-1 • integral x in 0..2*pi, f(-pi+x)
  = integral t in -1/2..1/2, f(-2*pi*t).
```

It is obtained only from `integral_comp_add_left` and
`integral_comp_sub_mul`; no boundary equality is assumed.  Iterating it over
`Fin 4` must expose four literal Jacobian factors and then prove
`((2*pi)^-1)^4 = ((2*pi)^4)^-1`.  The existing finite-product Fubini
infrastructure in `IntervalIntegralPiCoordinateTransport` is the preferred
lifting route.  This separates three facts that must not be conflated:

1. the `Icc` face seam makes the descended torus function continuous;
2. `measurePreserving_mk (-1/2)` pulls Haar measure back to centered `Ioc`;
3. the affine slice identity produces the source normalization and the
   literal translated Brillouin parameter.

The preferred implementation now packages item 3 as a measure-preserving
map rather than manually iterating four Fubini rewrites.  Static candidate:
`tmp/BalabanCMP89NormalizedBrillouinToTorusMeasure.draft.lean`.

Define the one-coordinate normalized source measure

```
nu1 = ofReal((2*pi)^-1) • volume.restrict(Ioc 0 (2*pi))
```

and the physical-to-torus map

```
x |-> (1/2 - x/(2*pi) : UnitAddCircle).
```

The proof factors through four separately auditable maps:

1. `x |-> x/(2*pi)` sends `nu1` to `volume.restrict(Ioc 0 1)`;
2. `AddCircle.measurePreserving_mk 1 0` sends that interval to Haar;
3. negation preserves Haar;
4. translation by `1/2` preserves Haar.

Taking the `Fin 4` product yields the torus map.  A separate finite-product
measure lemma proves

```
Measure.pi (fun _ => nu1) =
  ofReal((2*pi)^-1)^4 •
    cmp89Eq249FourDimensionalBrillouinMeasure.
```

Thus the public integral theorem returns the literal
`cmp89Eq249NormalizedFourDimensionalBrillouinIntegral`; it does not merely
return an equivalent centered-cube integral.  Finally, the exact arithmetic
identity

```
-2*pi*(1/2 - x/(2*pi)) = -pi+x
```

identifies the momentum with
`cmp89Eq251PhysicalBrillouinParameter`.  This removes the opposite-half-open
boundary comparison from the physical endpoint proof: it is already encoded
in the normalized source measure, while the topological seam remains the
reason the torus lift is continuous.

## Static G23.3 physical specialization

Once the generic centered-cube quotient and the mass-uniform fine-lattice
face seam are promoted, specialize them with the raw cube function

```
greenCube(L,j,mass,a,u)(t) =
  cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
    4 L j mass a
    (fun mu => -2*pi*(t mu))
    (cmp89Eq249PhysicalFineLatticeDisplacement
      (((L^j : Nat) : Real)^-1) u).
```

The specialization has three separate public gates.

1. **Cube continuity.**  Derive continuity from
   `continuousAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_real_massUniform`
   and the continuous affine map `t |-> -2*pi*t`.  Do not accept a continuous
   cube family from the caller.
2. **Coordinate seam.**  For the face-replacement cube `z`, use the lower
   physical face `p nu = -pi` at `t nu = +1/2`.  The physical period shift
   sends it to `+pi`, which is exactly `t nu = -1/2`.  Consume the named
   mass-uniform fine-lattice boundary seam, then orient the equality to the
   generic quotient's convention

   ```
   greenCube (update z nu (-1/2)) =
     greenCube (update z nu (+1/2)).
   ```

   The sign reversal is forced by `p(t) = -2*pi*t`; it must be visible in
   the proof rather than closed by an unexplained `simpa`.
3. **Exact pullback.**  Define the descended continuous torus Green by
   `cmp89CenteredUnitCubeLift greenCube seam` and expose the exact theorem

   ```
   torusGreen (cmp89CenteredUnitCubeToTorus t) = greenCube t.
   ```

   No global periodicity, arbitrary `FactorsThrough` witness or value at a
   removable singularity may appear in the public signature.

Two later dictionaries are deliberately *not* part of this specialization.

- **Finite sample dictionary.**  The canonical centered representative of
  `ell/N'` must be transported to the literal Step-8b.21 momentum
  `-2*pi*ell/N'`.  For `ell != 0`, this is a source-specific physical-period
  reindexing on the proved nonsingular domain.  For `ell = 0`, use the
  sealed zero-fibre branch.  The face seam alone does not prove this
  interior representative transport.
- **Fourier coefficient dictionary.**  The exact orientation gate is the
  identity in `tmp/BalabanCMP89CenteredTorusFourierPhase.draft.lean`:
  Mathlib's `mFourier (-n)` and `p(t) = -2*pi*t` produce the positive
  displacement `(u + M*n)/M`.  This must remain a named theorem before the
  integral is identified with the literal normalized Green coefficient.

These separations prevent a green quotient constructor from being reported
as either the Step-8b.21 sample theorem or the Step-8b.22 coefficient
specialization.  Both dictionaries remain physical obligations.

### Exact centered sample representative

The existing CMP99 centered integer is the representative of `-ell mod N'`:

```
a_ell(mu) = cmp99SourceFlatQprimeCenteredCoarseAlias ell mu.
```

Therefore the centered cube representative of the **positive** torus sample
`ell/N'` is not `a_ell/N'` but

```
t_ell(mu) = -a_ell(mu)/N'.
```

This choice has the two required exact properties:

```
cmp89CenteredUnitCubeToTorus t_ell = ell/N' mod Z,
cmp89Eq248NegativeTwoPiTorusMomentum t_ell =
  cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell.
```

The first proof must consume
`cmp99SourceFlatQprimeSignedCenteredAlias_add_quotient_dvd`; the second is
literal field arithmetic.  Using `+a_ell/N'` would silently sample the
Fourier-negated coarse mode.

The continuous/discrete character comparison is a third exact property:

```
mFourier n (torusSample ell) =
  cmp99FlatZModFourierCharacter
    (cmp99FinBoxZModEquiv 4 N' ell)
    (cmp99FlatIntegerResidue n).
```

It is isolated in
`tmp/BalabanCMP99CenteredTorusSampleDictionary.draft.lean`.  This prevents
the Step-8b.22 finite sample from being identified with the torus evaluation
by convention alone: both use the positive character, and the equality is
proved coordinatewise from `fourier_coe_apply` and `ZMod.stdAddChar_coe`.

For the nonzero sample branch, the remaining transport is finite and must be
named explicitly:

1. obtain `w : Fin 4 -> Int` from
   `cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods`;
2. extend the one-coordinate fine-lattice period theorem to arbitrary
   coordinatewise integer periods using `Function.Periodic.zsmul` and the
   finite sum of coordinate periods;
3. derive every nonvanishing premise at the centered momentum from
   `cmp99SourceFlatQprimeCenteredAliasFibreNonvanishing`, then transport the
   literal stabilized Green endpoint through `w`;
4. conclude that the descended torus sample equals the Step-8b.21 endpoint
   at `cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell`.

For `ell = 0`, do not invoke the nonzero quotient or cancel the central
symbol.  Reduce `t_ell` and the literal base momentum to zero directly.  The
final public sample theorem may be total, but its proof must retain this case
split.

The static implementation is now isolated in
`tmp/BalabanCMP99CenteredTorusPhysicalGreenSampleTransport.draft.lean`.  It
packages the exact `unit`/`reduced`/`fine` displayed-domain predicates at
both endpoints, exits the stabilized quotient to the displayed sum before
using vector periodicity, and re-enters only after the physical domain has
been constructed.  It contains no Fourier-negation rewrite.

### Alias-aware Fourier-coefficient phase gate

The base orientation identity alone is insufficient for the literal Green:
its finite numerator is a sum over momenta

```
q_m(t) = p(t) + 2*pi*m.
```

Before distributing the Fourier character through that sum, prove publicly
that every reciprocal alias is invisible at an integer displacement:

```
exp(i * phase(q_m(t), n)) = exp(i * phase(p(t), n)).
```

This is not a new periodicity axiom.  It is the existing theorem
`exp_I_cmp89Eq251EntirePhase_add_int_aliasPeriods_physicalFine` specialized
to `N = 1`.  Combining it with the base negative-character convention and
the exact affine-residue identity gives, for every alias `m`,

```
mFourier(-n)(t) * exp(i * phase(q_m(t), u/M))
  = exp(i * phase(q_m(t), (u + M*n)/M)).
```

Lift this equality first through one literal bare numerator, then by
`Finset.mul_sum` through the stabilized finite alias numerator, and only then
through the common endpoint-independent denominator.  The static statement
ladder is in
`tmp/BalabanCMP89CenteredTorusGreenCoefficientPhase.draft.lean`.

This gate rules out a silent but plausible error: applying the base phase
identity directly to the Green sum would drop the factors
`exp(i*2*pi*m dot n)` without ever proving that they are one.  No parity,
alias-set symmetry or reindexing is needed or permitted at this step.

### Finite completion ladder from the torus Green to Step 8b.22

The remaining coefficient/application route is now a finite sequence of
source-shaped statements.  Static drafts exist for every item; none counts
as compiler evidence until promoted and cold-validated.

1. `BalabanCMP89Eq248GreenOneCoordinateContourShift.draft.lean` applies the
   boundary-seam rectangle theorem directly to the literal Green endpoint,
   using the mass-uniform holomorphy and fine-face seam producers.
2. `BalabanCMP89Eq248GreenProductContourTelescope.draft.lean` constructs
   partial-stage integrability internally on the compact Brillouin cube and
   telescopes the four coordinate shifts.  No endpoint family or integral
   equality is a premise.
3. `BalabanCMP89Eq248MassUniformNormalizedGreenBound.draft.lean` combines
   that contour equality with the literal pointwise Green majorant.  The
   `(2*pi)^(-4)` source normalization cancels the cube volume exactly.
4. `BalabanCMP89CenteredTorusGreenCoefficientPhase.draft.lean` proves the
   alias-aware character identity and lifts it through the finite stabilized
   numerator and common denominator.
5. `BalabanCMP89CenteredTorusGreenCoefficientDictionary.draft.lean` builds
   the centered representative only on the physical cube, proves the
   pointwise identity there, then uses `ae_restrict_mem` for the normalized
   integral.  It yields the exact positive affine-residue Fourier
   coefficient; it asserts no off-cube identity.
6. `BalabanCMP89CenteredGreenFourierSummability.draft.lean` identifies the
   actual `mFourierCoeff` with that physical coefficient and proves absolute
   summability using the exact signed `l1` product majorant at owner rate.
   This is sufficient for Fourier reconstruction, but its earlier
   reverse-triangle residue bound is **not** the physical `B0` estimate: its
   representative prefactor grows like `exp ((rho/K) * ||u||_1)` and hence
   discards the required owner displacement decay.
7. `BalabanCMP99PhysicalGreenFiniteGridAliasing.draft.lean` invokes Mathlib's
   Fourier reconstruction for the actual continuous torus Green, identifies
   each positive finite sample character, and only then applies Step 8b.22.
   Its final theorem consumes the separate centered-to-physical sample
   transport, so the left side is the normalized DFT of literal uncentered
   CMP99 Green samples and the right side is the literal normalized physical
   Green summed over the selected integer residue class.

The nonzero/zero finite-sample transport from the descended torus Green to
CMP99's uncentered physical momentum now has the separate static draft named
above.  It remains outside the generic aliasing theorem and does not count as
compiler evidence until promoted and cold-validated.

### Centered periodic residue estimate after Step 8b.22

The physical `B0` route must not consume the growing-prefactor theorem
`tsum_cmp89SignedLatticeL1ExponentialWeight_physicalResidue_four_le`.
Instead it first centers the physical endpoint displacement modulo the full
period `P = K*N` and then sums the exact residue fibre.  Coordinatewise, if
`2*|u_c| <= P`,

```
sum_m exp (-delta * |u_c + P*m|)
  <= (2 / (1 - exp (-delta*P))) * exp (-delta*|u_c|).
```

The proof separates the positive and negative halves of `Int`; centeredness
is used only on the opposite half.  Product factorization then gives

```
sum_{m : Z^d} exp (-delta * ||u_c + P*m||_1)
  <= (2 / (1 - exp (-delta*P)))^d * exp (-delta*||u_c||_1).
```

At `delta = rho/K` and `P = K*N`, the geometric ratio is
`exp (-rho*N) <= exp (-rho)`.  Thus the constant is uniform in `N`, there is
no `(K*N)^d` volume factor, and the conclusion retains the literal decay
`exp (-(rho/K) * ||u_c||_1)`.  The static proof ladder is in
`tmp/BalabanCMP89CenteredPeriodicL1ResidueSum.draft.lean`.

One dictionary remains before this estimate can feed the regional owner
metric.  For the literal endpoint displacement `u = x - K*y`, construct a
named centered representative `u_c` modulo `P = K*N` and an integer vector
`w` with

```
u = u_c + P*w,
2*|(u_c)_mu| <= P.
```

The Step-8b.22 residue-zero selector then becomes
`u + P*m = u_c + P*(w+m)` by an explicit translation equivalence on
`Z^4`.  This affine carry, rather than a mental identification of residue
classes, is the next source-shaped bridge.  Only after it is compiled may
the periodic `l1` decay be converted to the named owner distance and used in
the physical `B0` producer.

The source-specific composition is isolated in
`tmp/BalabanCMP99PhysicalGreenZeroResidueBound.draft.lean`.  It derives the
literal zero-mass Green coefficient majorant from the mass-uniform contour
bound, applies the residue-zero reindexing, and bounds both the sum of norms
and the norm of the selected complex coefficient sum.  Its public decay is
still expressed in the canonical centered representative.  It deliberately
stops before identifying that representative with a literal physical-site
displacement or any owner metric.

That final identification has an even-period seam gate.  CMP89's printed
centered carrier uses a fixed half-open interval, whereas `ZMod.valMinAbs`
may choose the opposite sign for the antipodal residue when the period is
even.  Therefore the next consumer must **not** assert equality of the two
signed representatives.  It must prove only the load-bearing statement:
their coordinatewise `natAbs` values (hence their `l1` lengths and
exponential weights) agree because both realize `zmodCircVal` of the same
residue.  The sign at the antipode is irrelevant to the bound but is not
definitionally interchangeable.

There is a second, load-bearing scale gate.  The current finite synthesis is
on the diagonal Gate-7 carrier: its period is `P = K*N` and its natural owner
blocks have side `K`.  CMP99's final source-localization owner instead has
side `L^(depth+1)` on `2*(K*Q)` owners.  Therefore this bridge closes only
item 4 of the recorded post-Gate-7 route.  It must not be fed directly to
`cmp99Eq389SourceLocalizationOwner_mul_dist_le_transportL1_add_boundary`
until item 5 has re-instantiated/generalized the carrier from diagonal
`K = L = M` to independent source scales `(L,K)`.  The sealed `valMinAbs`
and fine-to-owner lemmas remain reusable after that dictionary, but they do
not erase the scale-separation obligation.

The diagonal item-4 endpoint is now written statically in
`tmp/BalabanCMP99DiagonalFiniteGreenOwnerBound.draft.lean`.  It uses the
shortest signed periodic displacement, proves that re-centering preserves
its `l1` length across the antipodal seam, pays the two block-boundary costs
as the explicit factor `exp (2*rho)`, and bounds the norm of the actual
residue-zero Green coefficient sum by diagonal owner decay.  Its carrier is
still `FinBox 4 (K*N)` with owner side `K`; this exact type is the guard that
prevents the theorem from masquerading as the independent-scale item 5.
