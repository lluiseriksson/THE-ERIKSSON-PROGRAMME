# hRpoly CMP102 → CMP116 vertical slice

**Date:** 2026-07-28  
**Branch:** `codex/cmp116-interacting-wilson-hessian`  
**Baseline audited:** `d8856a76`

## Purpose

This document replaces job count by a consumer-facing progress metric.  A
checkpoint counts as progress toward the terminal CMP116 theorem only when it
constructs, or removes a hypothesis from, one of the objects consumed by

```lean
cmp116Eq226PhysicalContour_singleScaleUVDecay_boundedHoles_of_boundaries
```

The terminal boundary objects are:

1. a physical contour source family `S`;
2. `CMP116Lemma3Eq229ScaleBoundary`;
3. `CMP116Lemma3PStageSourceScaleBoundary`;
4. `CMP116Lemma3WeightedPostPSourceScaleBoundary`;
5. the scalar decay profile `hprofile`.

The fifth item contains the target time profile
`Real.exp (-(c0 * (t : ℝ)))`; it must therefore be generated from source
parameters rather than treated as a harmless bookkeeping premise.

## Import-graph audit

Before the bridge module introduced after `d8856a76`, no file whose basename
was outside the `BalabanCMP102*` family imported a `BalabanCMP102*` module.
The terminal theorem occurred only in its definition file and its audit file.
Consequently, the CMP102 producer lane compiled but did not feed the CMP116
consumer lane.

The first exact type bridge is now:

```lean
cmp102FineFieldEquivCMP116PhysicalGaugeField
```

in `BalabanCMP116CMP102PhysicalFieldBridge.lean`.  It identifies the plain
physical positive-bond field used by CMP116 with the `PiLp 2` realization
used by CMP102, proves coordinate equality, and proves both round trips.
This bridge discharges no analytic boundary by itself.

## `CMP116Eq226PhysicalContourTermSource` field audit

The source record is the first object that must be constructed physically.
Its current status against the CMP102 lane is:

| Record component | CMP102 producer status |
|---|---|
| `contour` | **missing seed globally**: every current constructor transforms an existing density; no lane constructs a closed initial `CMP116Eq214PhysicalContourDensity` |
| `source` | physical Gamma/operator ingredients exist, but no equality installs them in the contour density |
| `domainMetric`, `domainSupport` | domain geometry exists on the CMP102 side; no typed equality to the contour index family |
| Cauchy-radius identities | generic CMP116 formulas exist; not instantiated by a CMP102 contour producer |
| positivity/smallness scalars | many scalar lemmas exist; no complete source record |
| `outer_bound` | no CMP102-to-contour theorem |
| `inner_bound` | no CMP102-to-contour theorem |
| contour `potential` summand | **partially constructed**: the complete CMP102 equation-(80) radial operator is installed, and its fixed quadratic part `Q₈₀(0)` is now separated exactly from the genuine field-dependent residual `Q₈₀(B) - Q₈₀(0)`; the Lemma-1 residual family is separately domain-indexed; the literal cutoff now keeps every radial point of each selected domain projection inside the source small-field ball; the physical third-jet decay, remaining source summands, and (1.36) are open |
| `interaction_bound` | **open**: its terminal residual is `cmp116Eq220ResidualDomainWeight`, so it requires a concrete `V''_k` satisfying (1.36); closing the `Q_Y` branch through (1.43)/(2.19) does not discharge this field |
| `source_bound` | operator/source bounds exist parametrically; no installed contour source |
| `domain_nonempty`, `domain_subset` | geometric ingredients exist; no source-record construction |
| `rooted_residual` | **missing source instance** |
| `volume_budget` | **missing source instance** |

Therefore:

```text
physical CMP116Eq226PhysicalContourTermSource constructed: 0
terminal boundary objects discharged from CMP102:          0 / 5
terminal theorem instantiated nontrivially:                 0
```

## Closed CMP102 result retained

The literal reconstructed fine-head-tail domain FTC contribution now has:

1. a source-derived second field derivative;
2. `ContDiff ℝ 2`;
3. value zero at the zero field;
4. Fréchet derivative zero at the zero field;
5. an exact radial identity

```text
F_Y(A) = (1 / 2) * inner A (Q_Y(A) A).
```

This is a valid producer-side theorem.  It is not yet the CMP116 residual
bound and must not be counted as a discharged terminal hypothesis.

## Estimate discipline: equations (1.36) and (1.43)

The two source estimates must not be identified:

* `cmp116Eq136ResidualMajorant` bounds the residual `V''_k(Y,B)`;
* `cmp116Eq143QMajorant` bounds matrix elements of the radial quadratic
  operator `Q(Y,B;b,b')`.

Consequently, an operator-norm theorem placing
`cmp102Eq80PhysicalFineHeadTailDomainFTCRadialOperator` below
`cmp116Eq136ResidualMajorant` would mix distinct source objects.  The
source-faithful radial target is instead an equation-(1.43) matrix-element
bound obtained from the literal Hessian along the segment `t • B`.  The
generic no-loss transfer from such a Hessian estimate to the radial operator
already exists in `BalabanCMP116RadialTaylorBound.lean`.  The literal bridge
is now closed by:

```lean
cmp116FDerivHessian_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
abs_inner_cmp102Eq80PhysicalFineHeadTailDomainFTCRadialOperator_le_eq143
```

in `BalabanCMP102Eq80PhysicalDomainFTCEq143Frontier.lean`.  The first theorem
identifies the Hessian with the reconstructed CMP102
`SecondFieldDerivative`; the second transfers an equation-(1.43) bound on
that concrete derivative to the installed radial operator without loss.
The remaining work is to derive the explicit matrix-element premise from
the CMP102 source jets and domain-decay producers.  The first quantitative
part of that derivation is now closed in
`BalabanCMP102Eq80PhysicalDomainFTCSecondFieldSourceMetricBound.lean`:

```lean
norm_cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative_le_sourceMetric
abs_inner_cmp102Eq80PhysicalFineHeadTailDomainFTCRadialOperator_le_sourceMetric
```

It integrates the existing order-three source-jet estimate through the
literal affine FTC and multiplies it by the already proved
cardinality/tree-metric decay of the reconstructed domain coefficient.  Its
right-hand side is the explicit producer-side quantity
`cmp102Eq80PhysicalDomainFTCSecondFieldSourceMetricMajorant`.  The second
endpoint applies that estimate uniformly along the radial segment and
produces the corresponding matrix-element bound for the literal radial
operator, retaining the two probe norms and introducing no equation-(1.43)
assumption.  The remaining equation-(1.43) step is therefore the physical
production of the uniform source-jet inputs and the scalar comparison of
this explicit majorant with the printed constants `C3`, `epsilon1`, `C2`,
and `kappa1`.

That scalar comparison is now isolated in
`BalabanCMP102Eq80PhysicalDomainFTCEq143SourceMetric.lean`.  It selects

```text
kappaCard   = (kappa1 - 1) * Msource^(-4) / 2
kappaMetric = (kappa1 - 1) / 8
```

and removes every dependence on `Y` from the remaining producer budget.
The reconstruction offsets `exp(kappaCard * 10000)` and
`exp(kappaMetric * 10000)` remain visible in that budget.  They are fixed
smallness thresholds on the walk ratios, not additional decay in the domain
metric.

The role of `10000` must nevertheless be stated precisely.  It is the proved
uniform upper budget for the large-block carrier contributed by one literal
walk unit, not a replacement for `domainMetric Y`.  The source-metric
reassembly uses the number of walk units together with the cardinality and
tree-metric lower budgets to produce the genuine final factors

```text
exp (-kappaCard * Y.blocks.card)
  * exp (-kappaMetric * cmp116CubeEdgeTreeMetric Y).
```

Thus the premises

```text
cardRatio   <= exp (-kappaCard * 10000)
metricRatio <= exp (-kappaMetric * 10000)
```

are per-unit contraction requirements.  They are not themselves
domain-decay statements, but the terminal prefactor derived from them does
decay in the two literal domain observables.  Neither premise may be
described as a bound in `d_k(Y)` before that reassembly step.

The scalar cancellation

```text
tau radius (2.18) * residual majorant (1.36)
  = residual domain weight (2.20)
```

is already proved separately in `BalabanCMP116Eq136To220.lean`.  It applies
to `V''_k`, not to the radial operator.

## Next acceptance target

The immediate source-facing target is the missing **residual `V''_k`**.
The repository currently contains
`cmp102Eq80SourcePi4FullyDecoupledResidual`, but that object is only the
all-zero weakening leaf of the equation-(80) sector.  It cannot be identified
with `V''_k`: the latter belongs to the complete localized fluctuation action,
includes the independently localized Lemma-1 energy-difference sector, and
must satisfy (1.36).

The source-faithful split is therefore:

```text
Q_Y branch:
  literal CMP102 connected equation-(80) activity
    -> radial Hessian average -> (1.43) -> (2.19)

V''_k branch:
  complete localized fluctuation action
    - quadratic core selected above
    -> concrete residual -> (1.36) -> (2.20)
```

The primary CMP116 proof makes this residual branch more precise.  Domain by
domain, `V''_k` has two source families:

```text
V''_k(Y)
  = localized Lemma-1 energy-difference activity V'_k(Y)
    + directly bounded F^(k) residual terms assigned to Y.
```

The terms of `F^(k)` carrying a dangerous negative power of `g_k` are the
ones expanded to second order and assigned to `Q(Y,B)`.  They are not a
producer of the Lemma-1 family.  Consequently there is no source-faithful
comparison

```text
cmp116Eq143QMajorant -> cmp116Eq136ResidualMajorant.
```

Any such comparison would conflate the two summands of (1.42).

There is a second distinction which must remain explicit.  The all-zero
weakening branch

```text
cmp102Eq80SourcePi4FullyDecoupledResidual
```

is a leaf of the FTC expansion in the weakening coordinates.  Despite the
legacy identifier, it is not the Taylor residual in the physical field
`B`.  In particular:

```text
weakening FTC:  coupled value = all-zero leaf + connected increments;
field Taylor:   localized V_k = quadratic core + V''_k.
```

These are decompositions in different variables.  The all-zero leaf is a
single anchored scalar, whereas the source residual is a family indexed by
localization domains.  A valid construction of `V''_k` must therefore
provide the missing domain assignment and prove (1.36); it cannot obtain
either fact by renaming the FTC leaf.

`BalabanCMP102Eq80SourcePi4DecoupledLeafRadial.lean` makes this distinction
formal rather than merely terminological.  It gives the legacy all-zero
branch the source-honest alias
`cmp102Eq80SourcePi4FullyDecoupledLeaf`, proves its `C²`, value-zero, and
first-derivative-zero normalizations in the physical field, and constructs
its exact field-radial Hessian operator.  Adding this operator to the
connected-domain radial sum yields the literal identity

```text
equation-(80) physical potential
  = (1/2) <B, CompleteRadialQuadratic(B) B>.
```

Consequently the entire equation-(80) sector is installed in one exact
radial representation, but this does **not** make it a fixed quadratic
functional: `CompleteRadialQuadratic(B)` depends on `B`.  The source-facing
split must instead distinguish

```text
fixed quadratic part = Q₈₀(0),
equation-(80) residual operator = Q₈₀(B) - Q₈₀(0).
```

`BalabanCMP116RadialTaylorResidual.lean` constructs this difference in
general, identifies `Q_f(0)` exactly with the Fréchet Hessian at the origin,
and writes its matrix elements as the radial average of
`D²f(tB) - D²f(0)`.  Instantiating it with the already constructed complete
equation-(80) operator and consuming the existing exact radial identity gives
the scalar split into the fixed quadratic term and the genuine residual term.
This identifies a canonical equation-(80) candidate summand for `V''_k`;
it is not yet the source-level `V''_k`, and it does not prove its
equation-(1.36) bound.  That identification still requires the domain/scale
assembly, while the bound requires a quantitative modulus for the variation
of the physical Hessian along the segment.  Independently, the complete
radial operator can become Balaban's source `Q(Y,B)` only after the domain
dictionary and the matrix-element estimate (1.43) are proved.

The same module records the exact third-order gain that the future producer
must preserve.  If

```text
|D²f(tB)[A',A] - D²f(0)[A',A]|
  <= Lambda(Y) * t * ||B|| * ||A|| * ||A'||,
```

then Lean proves

```text
|<A, (Q_f(B)-Q_f(0)) A'>|
  <= (Lambda(Y)/3) * ||B|| * ||A|| * ||A'||,

|(1/2)<B, (Q_f(B)-Q_f(0)) B>|
  <= (Lambda(Y)/6) * ||B||^3.
```

The constants come from
`2 * integral_0^1 (1-t)t dt = 1/3`.  This does not yet prove (1.36):
`Lambda(Y)` must be produced from the literal equation-(80) third-jet
chain with the source-metric decay, rather than supplied as a free
domain-independent scalar.

`BalabanCMP116RadialHessianThirdJet.lean` now removes the free radial
Hessian-modulus premise from this generic step.  From `f ∈ C³` and a bound
on the literal third Fréchet derivative at every point of `[0,B]`, it derives
the required Hessian difference by a Banach-space mean-value theorem and
then obtains the displayed `Lambda/3` and `Lambda/6` estimates.  Thus the
generic order-three gain is complete.  The physical counter remains open:
the bound on the third derivative must still be instantiated by a
domain-dependent `Lambda(Y)` with the source metric and cardinality decay.

`BalabanCMP102Eq80SourcePi4RadialPackage.lean` removes an independent
elaboration obstacle before that specialization.  It stores the literal
equation-(80) data, regularity, origin normalizations, patch certificate,
and contour restrictions in one dependent record, then exposes the
physical potential, the complete radial operator, and their exact quadratic
identity through short projections.  This is interface compression only:
it does not supply `Lambda(Y)` or move any terminal analytic-boundary field.

There is a separate source/consumer mismatch that must be resolved before
specializing the cubic estimate.  CMP116 proves (1.36) on the small-field
analytic domain (`|B'| <= C1 * epsilon1`), whereas both
`CMP116Eq226PhysicalContourTermSource.interaction_bound` and the corrected
conditioned record's `remainder_bound` quantify over every Gaussian
coordinate vector.  The corrected conditioned route weakens the interaction
inequality itself to an almost-everywhere statement and reaches the
Lemma-3 boundary, but it still assumes the residual estimate uniformly in
that unbounded vector.  Consequently the generic cubic bound cannot yet be
installed source-faithfully: one must either prove a global quadratic-growth
bound for the assembled potential, or formalize the small-field/large-field
decomposition that restricts use of (1.36).  No such bridge is currently
present, so `interaction_bound` remains at `0/5`.

`BalabanCMP116Eq222CutoffSupportInteraction.lean` removes the artificial
global quantifier at the Gaussian-consumer layer.  If the literal cutoff is
zero, the inner integrand is zero; otherwise the module requires the
interaction estimate only on that support and carries it through the
almost-everywhere domination and the integrated equation-(2.24) majorant.
It also proves directly that nonvanishing of the complete cutoff implies
`||bondField b e|| < threshold` for every `e ∈ Y0`.  The remaining
source-facing bridge is now precise: transport these bondwise inequalities
to the norm bound on the assembled `B'` used by (1.36), including whatever
collar/support relation is needed between `Y0`, `Z0`, and the domain `Y`.
This does not yet move the terminal `interaction_bound` counter.

`BalabanCMP116Eq222CutoffSupNormTransport.lean` closes the norm-transport
part of that bridge.  For every physical bond carrier `S ⊆ Y0`, nonvanishing
of the literal signed cutoff implies

```text
cmp98SourceFieldSupNorm
  (physicalBondProjection S (cmp116SourcePhysicalCoordinateCochain b))
    ≤ threshold.
```

This uses the already certified `PiLp ∞` realization of the source norm, so
there is no ambient-volume or support-cardinality loss.  It also answers the
unbounded-`b` objection precisely: outside cutoff support the integrand is
zero, while on cutoff support every localized field whose carrier lies in
`Y0` remains in the printed small-field ball.  The theorem does not claim
that the entire interior-bond carrier of `Z0` lies in `Y0`; the remaining
source obligation is the locality dictionary showing that each equation-(80)
residual indexed by `Y` reads a carrier `S(Y) ⊆ Y0`.  Until that dictionary
and the physical third-jet decay are installed, `interaction_bound` remains
at `0/5`.

`BalabanCMP102Eq80SourcePi4CutoffCarrier.lean` then constructs the missing
inclusion rather than receiving it as a premise.  Every connected physical
equation-(80) label is converted to the literal
`CMP116LocalizationDomain M (2*Q)` with the same block carrier.  For a
selected finite family `D`, its source cutoff carrier is defined by

```text
Y0(D) = union over W in D of bondSupport(W),
```

where `bondSupport(W)` requires both physical endpoints to lie in `W`.
Lean proves `bondSupport(W) ⊆ Y0(D)` for every `W ∈ D`, and combines this
with the cutoff theorem to obtain the source sup-norm bound on the field
projected to `bondSupport(W)`.  Thus the geometric inclusion and the norm
transport are now physical end to end.

An audit of the literal connected-activity definition rules out one tempting
but unjustified next step.  The current constructor accepts global functions
`D`, `D₃`, and `V₀`; its type supplies no locality certificate for them.
Consequently an equality asserting that the activity is unchanged after
projecting the ambient field to `bondSupport(W)` is not derivable from the
current interface.  Such an equality may only be introduced after the
source constructors of those functions prove the required locality.  It
must not be treated as a generic property of the FTC decomposition.

`BalabanCMP102Eq80CutoffRadialResidual.lean` takes the source-safe route that
is already available.  It proves exact homogeneity of
`cmp98SourceFieldSupNorm`, proves that its closed balls are star-shaped, and
therefore derives, on nonzero literal cutoff support,

```text
X in segment(0, projection_bondSupport(W)(B))
  -> cmp98SourceFieldSupNorm X <= threshold.
```

The terminal theorem consumes a third-jet estimate required only on this
small-field ball and feeds it directly into the exact `Lambda/6` cubic
radial-residual estimate.  Thus no global-in-the-Gaussian-coordinate
third-jet premise remains in this bridge.  The analytic frontier is now the
source construction of the domain-decaying third-jet bound on that ball
(or, equivalently, a source locality theorem strong enough to derive it),
followed by its scalar comparison with equation (1.36).

The first source-faithful producer for that analytic frontier is now present.
`BalabanCMP102Eq80SourcePi4ThirdFieldDerivative.lean` extracts the final three
physical-field variables directly from the literal joint equation-(80) jet:

```text
joint jet of order n+3
  -> three-variable physical continuous multilinear map
  -> norm <= joint-jet norm * product of propagator-direction norms.
```

`BalabanCMP102Eq80PhysicalDomainCoefficientThirdFieldDerivative.lean`
specializes this construction to the reconstructed rectangular domain
coefficient.  Its terminal estimate is

```text
norm(third field jet of the literal domain coefficient)
  <= order-four joint source-jet majorant(D,D3,V0)
       * norm(literal reconstructed domain matrix).
```

This is a genuine physical producer: neither the complete third derivative
nor its bound is supplied as an input.  It also preserves the exact
source-metric factor carried by the reconstructed domain matrix.

The consumer-facing derivative identification is now also closed.  A
normed-space slice theorem and the exact order-one propagator extraction
give

```text
norm(iteratedFDeriv 3 of the literal reconstructed coefficient at A)
  <= norm(order-four joint equation-(80) jet at (H,A))
       * norm(literal reconstructed domain matrix).
```

The component source-jet majorant is then substituted on the right.  Thus
the cutoff theorem no longer has to consume a separate mixed-jet extractor:
its `iteratedFDeriv 3` object is the derivative of the literal reconstructed
coefficient function itself.  The remaining source obligation is a
**uniform small-field** order-four component-jet bound with the printed
domain decay, followed by the scalar comparison with equation (1.36).
Neither that bound nor the unrestricted Gaussian `interaction_bound` is
claimed here.

The quantitative implicit-function route to the missing component jets has
now advanced one derivative.  The selected physical correction satisfies a
literal fixed-point equation `g x = T (x, g x)`.  The new module
`QuantitativeFixedPointThirdDerivativeStability.lean` differentiates that
identity once and constructs the derived fixed-point map

```text
A -> DT(x,g(x)) o (id,A)
```

for `A = Dg(x)`.  Applying the already proved second-jet absorption theorem
to this literal map yields a third-jet bound for `g`; no estimate for `D3 g`
is assumed.  Two apparent auxiliary debts are eliminated internally:

```text
uniform bound on D2 g -> Lipschitz bound on Dg,
vertical contraction of T -> vertical contraction of the derived map.
```

The variation premise is also generated internally from a second derivative
of this *literal derived map*.  The source-useful endpoint does not ask for
that bound on arbitrary linear maps: it constructs the convex tube

```text
x in source domain,  norm(A) <= first-jet budget,
```

proves that `(x,Dg(x))` lies in it, and requires the derived-map second jet
only there.  By definition that derivative depends on jets of `T` only
through order three and on jets of `g` only through order two; it cannot
contain the target `D3 g`.  Consequently the only new source obligation is
an explicit tube-local bound for that derivative from the physical
second/third joint jets of `T`.  The existing first- and second-jet budgets
for `g` feed the recurrence directly.

The final assembly must also reconcile three domain index layers:

```text
Lemma-1 producer : CMP116LocalizationDomain 2 (L*N')
equation-(80)    : CMP116LocalizationDomain M (2*Q)
consumer        : Y : Fin nY with an explicit domainMetric
```

The consumer is abstract enough for a finite enumeration, but a
source-faithful scale dictionary must transport both producer families to
one `Fin nY` and identify its `domainMetric`.  No sum across these scales is
claimed before that dictionary exists.

The first representation layer of the Lemma-1 sector is now present in
`BalabanCMP109LocalizedActionExpansion.lean`.  It records the finite-volume
source form

```text
E_k = sum over (scale j, localization term X) of E^(j)(X),
```

with every term supported on the literal bilateral bond carrier of a
nonempty face-connected `CMP116LocalizationDomain`.  The term index is kept
separate from the domain so that different scales or source species may share
the same carrier.  For two physical gauge backgrounds, the module constructs
canonically the finite set of positive bonds on which their values differ and
proves the exact cancellation identity

```text
changed(U_perturbed,U_base) = {b : U_perturbed(b) != U_base(b)}

E_k(U_perturbed) - E_k(U_base)
  = sum over terms whose local support meets changed(U_perturbed,U_base)
      [E^(j)(X,U_perturbed) - E^(j)(X,U_base)].
```

It also proves that every surviving term's physical domain contains a changed
bond.  Thus neither the carrier nor the agreement-away-from-carrier property
is supplied by the caller.  This is the first source-faithful representation
of the energy difference, but it is not yet the analytic localization
estimate.

The physical fluctuation field entering this sector is now constructed in
`BalabanCMP109ConstraintCorrectionFixedPoint.lean` and
`BalabanCMP109ConstraintCorrectedFluctuation.lean`.  The first module proves
the volume-uniform source-sup bound

```text
|h D|_sup <= L^(d-1) |D|_sup
```

for the literal distinguished-bond right inverse `h`, and applies Banach's
theorem to the source equation

```text
D_tilde(A) = nonlinearCorrection(A - h D_tilde(A)).
```

This is intentionally a new fixed point: it does not reuse the different
CMP99 background minimizer `H`.  The second module defines

```text
B' = g_k C B - h D_tilde(g_k C B)
```

and proves that its flat block constraint is `-D_tilde` and that the complete
linear-plus-nonlinear block constraint vanishes exactly.

The corrected field is now installed into the first literal pair of
group-valued backgrounds displayed in CMP109 (2.12):

```text
E_k(U_k(exp(i [g_k C B - h D_tilde(g_k C B)]) V^(k)))
  - E_k(U_k(V^(k))).
```

The first genuine variational layer of `U_k` is now constructed in
`BalabanCMP109MinimalOrbitExistence.lean`.  For the literal one-step
decimation `2M -> M`, it proves:

```text
blockMap M : GaugeConfig d (2M) SU(Nc) -> GaugeConfig d M SU(Nc)
```

is surjective by an explicit positive-bond lift; every block fiber is compact;
the exact Wilson action is continuous on that fiber; and a chosen physical
background realizes the minimum.  Its public `SU(Nc)` endpoint receives only
the coarse background and satisfies both

```text
blockMap M (U_1(V)) = V
```

and the universal action-minimality inequality on that fiber.  It is not a
pointwise left variation.

`BalabanCMP109MultiscaleMinimalOrbitExistence.lean` now iterates this exact
construction through the literal factor-two tower.  It builds a right inverse
at every depth, proves the full block fiber compact and nonempty, and chooses
an `SU(Nc)` Wilson-action minimizer on that fiber.  No fine background,
constraint witness, compactness certificate, or minimizer is supplied by the
caller.

This remains only finite-volume variational existence.  The source `U_k`
still requires uniqueness of the regular minimizing gauge orbit, an
axial-gauge representative, and analytic dependence on the coarse
background.  Those stronger properties are exactly what permit the CMP109
(1.18) Cauchy/Lipschitz comparison.  Once the two regular backgrounds are
literal, that gain, together with rooted-domain resummation, must construct
the Lemma-1 residual family and contribute to the full `V''_k`.

`BalabanCMP109Lemma1PhysicalBackgrounds.lean` closes the first one-step
dictionary.  Banach produces `D_tilde` and its nonlinear chart; the file forms
the genuine special-unitary coarse field

```text
exp(i [g_k C B - h D_tilde]) V
```

and applies the proved one-step Wilson minimizer to that field and to `V`.
Both block equations are exact.  The resulting literal energy difference is
then rewritten as the sum over precisely those inductive local activities
whose support meets the canonical changed-positive-bond set.  No correction
field, perturbation carrier, or minimizer is supplied to the terminal
existence theorem.

`BalabanCMP109Lemma1ResidualFamily.lean` now performs the next exact source
step.  It takes the finite image of the domains actually carried by those
surviving inductive activities and defines

```text
V'_Lemma1(Y)
  = sum of the affected local-activity differences with domainOf(i) = Y.
```

Lean proves both

```text
E_k(U_perturbed) - E_k(U_base) = sum_Y V'_Lemma1(Y)
```

and that a domain outside the canonical affected-domain image contributes
zero.  This is a literal domain-indexed residual family, not an arbitrary
`remainder` supplied by the caller.  It is one source summand of `V''_k`;
the non-dangerous directly bounded terms of `F^(k)` remain to be added.
The only estimate used here is the triangle inequality inside each domain
fiber, so (1.36) is still neither assumed nor proved.

This advances the source dictionary but not the terminal analytic-boundary
count.  `CMP109LocalizedActionExpansion.activity` is intentionally an
arbitrary source local functional and carries no Lipschitz or decay data.
Consequently the first non-tautological analytic theorem must derive the
CMP109 (1.18) comparison for the regular axial-gauge minimizer and the
previous-scale localized activities.  Merely adding a Lipschitz field to the
record would rename that obligation and is not accepted.

The current checkpoint does **not** change the terminal score:
the physical `TermSource` remains unconstructed and zero of the five terminal
analytic boundaries are discharged.  A record which merely accepts an
arbitrary residual and an `h136` field would document the frontier but would
not count as discharging it.

The quantitative fixed-point route has nevertheless removed one generic
regularity obstruction.  `QuantitativeFixedPointDerivedMapSecondJet.lean`
uses the literal derived map

```text
(x,A) |-> DT(x,g(x)) o (id,A)
```

and proves that its graph factor is affine, with first-jet norm at most one
and identically zero second jet.  Consequently, on `|A| <= L1`,

```text
|D^2 fixedPointFirstDerivativeMap(x,A)|
  <= 2 C1 + C2 max(1,L1),
```

where `C1` and `C2` bound the first and second jets of the literal
coefficient `(x,A) |-> DT(x,g(x))`.  No third derivative of the fixed point
is assumed.

`QuantitativeFixedPointCoefficientJets.lean` now derives those two
coefficient budgets as well.  With

```text
R = max(max(1,L1),L2)
```

and a common bound `J` for the literal jets of `T` of orders one through
three at `(x,g(x))`, it proves

```text
|D coefficient|   <= J R,
|D^2 coefficient| <= 2 J R^2,

|D^2 fixedPointFirstDerivativeMap|
  <= 2(J R) + (2 J R^2) max(1,L1).
```

The graph-input jets are generated internally from `Dg` and `D^2g`.
Consequently neither `C1`, `C2`, nor `D^3 g` remains a generic premise.
`LocalQuantitativeComposition.lean` and
`QuantitativeFixedPointCoefficientJetsLocal.lean` close the local/global
regularity mismatch.  The composition estimate is now available from
`ContDiffAt` for the outer map at the physical graph point and global
smoothness only for the explicit graph input.  The same coefficient and
derived-map bounds therefore hold from

```text
ContDiffAt R 3 T (x,g(x)),
```

which is the regularity form already produced on admissible CMP102 charts;
no global smoothness of `T` is requested.

`BalabanCMP102PhysicalIntrinsicFixedPointJetZero.lean` now proves from the
literal CMP98 subtraction that the first derivative of the intrinsic
correction vanishes at zero, through the Lie-coordinate transport, the
physical sup-norm equivalence, and the joint source map.  Combining that
identity with the existing source-generated derivative-Lipschitz estimate,
`BalabanCMP102PhysicalIntrinsicFixedPointFirstJet.lean` produces

```text
|D T(p)| <= B_source |p|.
```

Thus the physical order-one joint jet is no longer a caller-supplied
budget.  `LocalSecondJetFromDerivativeLipschitz.lean` applies the converse
local mean-value estimate to the derivative map, and
`BalabanCMP102PhysicalIntrinsicFixedPointSecondJet.lean` verifies that the
physical source conditions persist in a neighborhood of every interior
chart point.  It consequently proves

```text
|D^2 T(p)| <= B_source
```

from strict source-radius and no-winding slack.  No second-jet budget is
supplied by the caller.  The order-three joint jet of the same literal map
is now the sole remaining `T` jet before the local coefficient endpoint
can be instantiated.  Taking it as an unexplained physical hypothesis
would only rename the obligation.

The order-three analytic primitives are no longer black boxes.
`AnalyticThirdDerivativeChangeOriginBound.lean` derives the full third
Fréchet derivative from the six permutations of the literal
changed-origin power-series coefficient and bounds that coefficient
uniformly on every strict sub-ball.  The specializations in
`NearLogExpThirdDerivativeChangeOriginBound.lean` consequently provide
source-generated third-jet budgets for both the Mercator logarithm and the
noncommutative exponential.  `LocalThirdJetFromSecondJetLipschitz.lean`
also records the exact final converse mean-value step.

The quantitative composition step is local on both sides.  The new
`norm_iteratedFDeriv_comp_le_at_of_both_local` endpoint shrinks the inner
chart to an open neighborhood whose image remains in the outer chart before
applying the within-set Faà di Bruno estimate.  In particular, transporting
the third jet through the Mercator logarithm no longer requires the false
global premise that the logarithm is smooth on the whole ambient matrix
space.

What remains at order three is therefore the physical ordered-product
assembly: propagate those primitive budgets through the Wilson line,
log/exp average, represented nonlinear block, fixed right normalizer,
physical coordinate map, and the literal shift.  No third jet of that
composite map is accepted as a premise.

The first physical transport is now closed.
`BalabanCMP102AmbientOrientedEdgeThirdJetBound.lean` proves that the literal
oriented edge `exp(Z_b) U_b` has every jet through order three bounded by one
generated strict-ball budget.  Bond evaluation is contractive, right
multiplication by the unitary background has norm at most one, and the
reverse-orientation conjugate transpose is also contractive.  Hence no
edge-level third-jet certificate remains.

`BalabanCMP102AmbientWilsonLineThirdJetBound.lean` now propagates those
source-generated jets through the complete noncommutative ordered product.
Matrix multiplication is bundled as a contractive real bilinear map and the
quantitative Leibniz rule gives one recursive budget for orders zero through
three.  Its only geometric input is the contour length; no ambient-volume
cardinality enters.

The next four layers are now closed as well.
`BalabanCMP102AmbientFourContourThirdJetBound.lean` first uses the literal
source collapse of the four-factor contour and bounds all positive jets
through order three by the physical source contour length.  The constant
identity term disappears automatically at positive order.
`BalabanCMP102AmbientLocalNearLogThirdJetBound.lean` transports those jets
through the locally analytic Mercator logarithm with the local Faà di Bruno
theorem.  `BalabanCMP102AmbientLogAverageThirdJetBound.lean` differentiates
the normalized finite block sum and cancels its exact cardinality
`|blockOf| = M^d`, so no block-volume factor survives.  Finally,
`BalabanCMP102AmbientExpAverageThirdJetBound.lean` transports the resulting
orders one through three through the literal noncommutative exponential.
All outer exponential jets come from its factorial power series; the
slightly enlarged radius used for the open second-derivative ball is
generated internally.

Thus the full `cmp98UbarExpAverage` third jet is physical and
volume-uniform.

`BalabanCMP102AmbientNonlinearBlockThirdJetBound.lean` now closes the next
ordered product.  It combines the exponential block average with the
straight coarse Wilson contour using the noncommutative quantitative
Leibniz rule on a genuine local Mercator neighborhood.  The common budget
controls all orders zero through three and depends only on source radii,
dimensions, and contour length.  No represented-block third derivative is
accepted from the caller.

The remaining physical transports before the order-three joint jet of `T`
are the fixed right normalizer, the physical coordinate map, and the
literal shift.

After that producer exists, the closed seed contour density can install both
the quadratic and residual branches and the concrete
`CMP116Eq226PhysicalContourTermSource` can discharge `interaction_bound`.

No theorem is to be accepted if it takes that equality, `interaction_bound`,
the complete `TermSource`, `hraw`, or `hprofile` as a renamed premise.

## Current centered-conditioned acceptance boundary

The centered conditioned lane reaches the same
`SingleScaleUVDecay (LocalizedCubeHsharpRemainder ...)` proposition as the
general lane after specializing to the physical dimension `d = 4`.  It does
not reduce the number of physical obligations: it replaces abstract
`outer_bound`, `inner_bound`, and `source_bound` assumptions by the explicit
coercivity, patched-parametrix, contour-series, Neumann, transpose-Neumann,
conditioned-root, and root-smallness certificates.

The cutoff-sensitive conditioned trace theorem now accepts the interaction
inequality almost everywhere for the conditioned Gaussian, but only as an
implication from the literal nonvanishing cutoff.  This is the correct
intersection of the covariance carrier and the small-field carrier.  Because
the producer controls that Gaussian measure, the terminal source record also
requires a quantitative lower covariance certificate:

```text
lambda_min > 0,
SInner nonempty,
lambda_min * <v,v> <= <v, conditionedCovariance v>
  for every v supported on SInner.
```

Thus the zero-root/Dirac-measure choice cannot discharge the almost-everywhere
interaction obligation vacuously.  The old pointwise theorem remains
available; the new interface is accepted only together with this named
nondegeneracy debt.

The scalar wall is now visible in the terminal data:

```text
(potentialRate + r2Rate + gamma) * ||conditionedRoot||^2 < 1.
```

For the physical coercive inverse this is controlled schematically by

```text
potentialRate + r2Rate + gamma
  <~ (min(1,a) - perturbation budget) / CP,
```

and in four dimensions the Poincare constant scales like the square of the
fixed block ratio, not the ambient volume.  This inequality, together with
`contour_series_small`, `neumann_small`, `neumann_transpose_small`, and the
patched-parametrix contraction, is a named open scalar frontier.

The analytic denominator is three, not four:

```text
potential_bound : open
r2_bound        : open
cutoff_energy_bound installed in the centered terminal record : open
```

`interaction_budget` is only the optimal normalization
`alpha = potentialRate + r2Rate + gamma`; it is not counted as an analytic
discharge.  No complete centered conditioned `TermSource` has yet been
constructed, and neither `hraw` nor `hRpoly` is proved.

## Equation-(80), the indexed cutoff estimate, and the missing residual

The canonical Pi4 indexing and the one-domain cutoff estimate are available,
but the latter has not been identified with Balaban's `V''_k`.

`BalabanCMP102Eq80SourcePi4DomainEnumeration.lean` canonically enumerates a
selected finite family

```text
D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor)
```

and supplies its literal localization domain, tree metric, block cardinality,
centered region, and bilateral support inclusion.  The indexed cutoff theorem
estimates the radial Taylor residual of an arbitrary supplied function after
the physical precomposition

```text
B |-> f (g_k C B)
```

and projection to the bond support of the individual domain.  This is a valid
conditional estimate, but no theorem identifies that radial residual with
`V''_k`.

The source-faithful finite Faà di Bruno lane already proves a stronger and
decisive identity for equation (80):

```text
equation80(B)
  = fullyDecoupledLeaf(B)
    + sum_W connectedDomainActivity(W,B)
  = (1/2) <B, completeRadialQuadratic(B) B>.
```

`BalabanCMP102Eq80SourcePi4DecoupledLeafRadial.lean` proves that even the
all-zero weakening leaf belongs to this field-radial quadratic sector.  Its
module documentation explicitly forbids identifying that leaf with
Balaban's residual.  Weakening order and field Taylor order are different
decompositions.

Consequently, lifting third derivatives through
`cmp102Eq80CorrectedPhysicalCompleteDomainFTCActivity` and its two `tsum`
layers would refine the quadratic-operator/(1.43) lane; it would not by itself
produce the residual majorant (1.36) consumed by `Eq220`.  The scalar
summability of the complete activity is also insufficient for differentiating
either `tsum`, so that lift remains a legitimate but separate Q-lane task.

The currently installed CMP116 potential still has two source mismatches:
`withCMP102FineHeadTailPotential` installs a bare fine-head/tail contribution
on the common `Z0` projection, whereas the indexed cutoff theorem concerns
`f (g_k C B)` on each individual domain support.  No equality between those
objects is asserted.  The finite Faà di Bruno reassembly gives the preferable
source dictionary for equation (80), so a new installer should use that exact
finite decomposition rather than select one summand or silently replace it by
the complete Neumann activity.

The residual frontier is therefore outside the equation-(80)-only identity:
one must construct the complete localized fluctuation activity of (1.41),
identify its quadratic `Q(Y,B)` contribution, and define the remaining
`V''_k(Y,B)` from the other fluctuation-action terms.  Only that literal
remainder may be compared with

```text
cmp116Eq136ResidualMajorant
```

and then summed into `cmp116Eq220ResidualDomainWeight`.

### The finite source list behind the missing residual

The primary CMP109 display (2.12) makes the missing family finite and
checkable.  Before localization, its `P^(k)` sector is the sum of the seven
displayed terms

```text
Tr log(I - h (delta D_tilde / delta B)(g_k C B))

+ log sigma(g_k C B - h D_tilde(g_k C B))

+ g_k^(-2) <H_1 h D_tilde_3(g_k C B), J>

- g_k^(-2) G_3(g_k B)

+ g_k^(-2)
    <H_1 g_k C B, Delta_1 H_1 h D_tilde(g_k C B)>

- g_k^(-2)
    <H_1 h D_tilde(g_k C B),
      Delta_1 H_1 h D_tilde(g_k C B)>

- g_k^(-2)
    V(H_1 (g_k C B - h D_tilde(g_k C B))).
```

The eighth displayed contribution is the curly-bracket energy difference

```text
E_k(U_k(exp(i [g_k C B - h D_tilde(g_k C B)]) V^(k)))
  - E_k(U_k(V^(k))).
```

CMP116 Lemma 1 localizes that eighth contribution into `V'_k(Y)` and proves
the bound (1.36).  CMP116 pages 10--11 then localize every term of `P^(k)`,
extract its second-order field Taylor form, and finally group equal domains.
Thus the source-faithful residual has the schematic finite form

```text
V''_k(Y)
  = V'_k(Y)
    + sum over the seven P^(k) species of
        (localized species at Y - its quadratic Taylor core).
```

This is stronger than the previous phrase “the other terms of `F^(k)`”:
the missing species and their signs are explicitly fixed by CMP109 (2.12).

The repository currently realizes only two portions of this list:

* `BalabanCMP109Lemma1ResidualFamily.lean` constructs and exactly regroups
  the `V'_k(Y)` family, but does not yet prove the CMP109 (1.18) analytic
  comparison that yields (1.36);
* the CMP102 equation-(80) development constructs the literal four-term
  functional `V`, its Pi4 localization, and its quadratic/radial identities.
  It has not yet installed the complete source term
  `-g_k^(-2) V(H_1(g_k C B - h D_tilde(g_k C B)))` with that sign, scaling,
  affine field substitution, and domain assignment into the CMP116 family.

No source-faithful constructors were found for the trace-Jacobian term,
`log sigma`, `G_3`, or the two displayed mixed correction pairings.  Generic
Jacobian budgets and contour determinant bounds elsewhere in the tree are
not definitions of these CMP109 terms.

There is nevertheless one additional source-faithful primitive below the
seven-term list.  `BalabanCMP109ConstraintCorrectionFixedPoint.lean` proves
existence and uniqueness in a certified ball for the literal CMP109 equation

```text
D = C(A - h D),
```

and `BalabanCMP109ConstraintCorrectedFluctuation.lean` defines

```text
B'(B,D) = g_k C B - h D
```

and proves the complete nonlinear block constraint when `D` is that fixed
point.  This is not yet the analytic map `B |-> D_tilde(g_k C B)` used in
CMP109 (2.12): the terminal producer is an existential theorem for each
field, and no repository definition chooses the unique solution as a
field-dependent function.  In particular, the tree currently has no
regularity theorem for the `h`-based fixed point as the input field varies.
The smooth implicit-function development for the background-minimizer
correction is a different fixed-point equation and cannot be substituted
definitionally.

This makes the first implementation dependency more precise:

```text
family of certified CMP109 correction data over A
  -> chosen unique function D_tilde(A)
  -> D_tilde(A) = C(A - h D_tilde(A))
  -> regularity / jets of D_tilde
  -> literal seven P^(k) species.
```

The first two arrows are a canonical choice from an already proved unique
existence theorem; the regularity arrow is analytic work.  Merely adding an
arbitrary function field called `D_tilde`, or reusing the unrelated
background-minimizer correction, would rename the missing source
construction.

The functional-analytic theorem itself need not be invented:
`isContDiffImplicitAt_fixedPoint_of_vertical_norm_lt_one` already turns a
jointly smooth fixed-point map with vertical derivative norm below one into
a smooth implicit function.  The source-specific obligation is to instantiate
it with

```text
(A,D) |-> C_intrinsic(A - h D),
```

where `h` is `cmp96ConstraintPivotInsertion`, and to prove the corresponding
joint smoothness and vertical derivative budget.  The existing CMP102
instantiation instead uses the background minimizer `H`; it is a proof
template, not the CMP109 map.

The term-by-term producer audit is therefore:

| CMP109 (2.12) species | Reusable substrate | Missing source theorem |
|---|---|---|
| `Tr log(I - h D D_tilde)` | finite matrix realization and `NearLog`/trace bounds | the analytic `D_tilde` map, its derivative, and the equality with this Jacobian |
| `log sigma(B')` | none specific to the axial-to-Landau change of variables | the literal Jacobian density `sigma` and its normalization/localization |
| `<H_1 h D_tilde_3,J>` | `h`, the correction fixed point, and generic jet calculus | the Taylor remainder `D_tilde_3` of that same correction and the source operator dictionary |
| `-G_3(g_k B)` | quadratic gauge-fixing operators only | the nonlinear gauge-fixing functional and its cubic remainder |
| `<H_1 g_k C B, Delta_1 H_1 h D_tilde>` | physical `C`, `h`, Hessian/covariance operators | exact `H_1`/`Delta_1` dictionary and the literal composed term |
| `-<H_1 h D_tilde, Delta_1 H_1 h D_tilde>` | the same operator substrate | the literal composed term with its printed sign and scaling |
| `-V(H_1 B')` | the equation-(80) four-term potential and its Pi4 localization | equality with this CMP109 species after corrected-field substitution, sign, `g_k^(-2)`, and domain regrouping |
| energy difference in braces | `BalabanCMP109Lemma1ResidualFamily.lean` | the source analytic comparison giving (1.36) |

The first row has an exact coordinate route once the local implicit branch
`g(A) = D_tilde(A)` has been constructed.  At a certified source point its
literal fine-field Jacobian is the endomorphism

```text
J_h(A)
  = cmp96ConstraintPivotInsertionCLM
      ∘ physicalGaugeOneCochainSupEquiv.symm
      ∘ Dg(A).
```

`BalabanCMP116PhysicalEndomorphismMatrix.lean` already transports a physical
fine-cochain endomorphism to the canonical bond--Lie matrix and preserves
composition and the identity exactly.  Therefore the source expression is
not an arbitrary determinant density: after proving the relevant Mercator
smallness it must be installed literally as

```text
trace (nearLog (-(cmp116PhysicalEndomorphismComplexMatrix J_h(A))))
```

because `nearLog X` represents `log(I + X)` and CMP109 prints
`Tr log(I - h D D_tilde)`.  The sign and the derivative evaluation point must
be checked in this form before localization.  Direct visual inspection of
CMP109 page 268, equation (2.12), confirms that the derivative of
`D_tilde` is evaluated at `g_k C B`; the displayed Jacobian does **not**
differentiate the outer substitution `B ↦ g_k C B`, so no extra `g_k C`
factor belongs in `J_h`.  The later covariance determinant is a different
object and cannot serve as this producer.

The symbol `h` also has a source-facing dictionary obligation.  The current
producer `cmp96ConstraintPivotInsertion` is proved to be the sparse right
inverse of the formalized **flat** block constraint.  CMP109 page 267
describes `h(c)` as `L⁻¹` times the inverse coefficient of the pivot variable
in the printed linear constraint `Q_tilde`.  If the corridor gauge makes that
coefficient definitionally equal to the flat scalar used by
`cmp96ConstraintPivotInsertion`, this must be stated and proved; otherwise
the background-dependent pivot coefficient has to be constructed.  The
right-inverse theorem for flat `Q` alone is not yet that source dictionary.
A direct construction that preserves the printed sparsity is:

```text
Qlin_U
  := physical Lie-coordinate form of
       [D(cmp102AmbientNonlinearBlock U)(0)] · block(U,0)⁻¹,
K_U
  := Qlin_U ∘ cmp96ConstraintPivotInsertion,
h_U
  := cmp96ConstraintPivotInsertion ∘ K_U⁻¹.
```

The required source lemmas are then `‖K_U-I‖<1`, the Neumann inverse,
`Qlin_U ∘ h_U = I`, pivot support, and block-diagonality of `K_U⁻¹`
(hence source-local dependence at each pivot).
At the trivial background one should prove `K_U=I`, recovering the current
flat insertion.  This route uses the literal linear term already subtracted
in `cmp102IntrinsicAmbientCorrectionBond`; it does not introduce a new
constraint operator by hypothesis.

The first algebraic part of this construction is now explicit.
`BalabanCMP109PhysicalLinearConstraint.lean` defines the displayed
`Qlin_U = L Q̃_U` from the raw Fréchet derivative of the represented
nonlinear block and defines its physical pivot response `K_U`.  This matches
the source identity `L Q̃ h = I`; no additional inverse block length belongs
in `Qlin_U`.
`BalabanCMP109PhysicalConstraintRightInverse.lean` names the defect
`K_U-I`, constructs its inverse as the convergent Neumann series, defines
a physical right-inverse candidate `h_U`, and proves the exact identity

```text
Qlin_U ∘ h_U = I
```

under the visible contraction `‖K_U-I‖<1`.  This does not discharge the
source estimate: the contraction, the trivial-background equality `K_U=I`,
and the block-diagonal/source-local dependence of the physical inverse remain
to be proved from the literal small background.  In particular the
contraction is not to be propagated as an endpoint hypothesis.
`BalabanCMP109PhysicalConstraintRightInverseSupport.lean` now proves
pointwise that `h_U D` vanishes away from the literal pivot image and that
its value at `b₀(c)` is exactly
`L^(d-1) • (K_U⁻¹ D)(c)`.  Thus fine-field pivot support is closed.  What is
still missing is the no-mixing theorem showing that `(K_U⁻¹ D)(c)` depends
only on `D(c)`; without it the candidate is not yet identified with the
printed local formula `hB(b₀(c)) = h(c)B(c)`.
The source-faithful next endpoint is therefore the off-diagonal vanishing

```text
c ≠ c'  =>
  (K_U (singlePhysicalBondCochain c v))(c') = 0.
```

It must be derived from the literal corridor paths and pivot geometry.  It
must not be replaced by a supplied diagonal certificate.  Once this is
proved, the diagonal coefficient of `K_U` can be inverted pointwise to
construct the printed Lie-algebra operator `h(c)`.

There is one non-definitional selection issue before this Jacobian is
available.  Intrinsic fixed points obtained from any two source certificates
at the **same** fine field agree: their zero-centred radii are comparable, so
the fixed point in the smaller certified ball also lies in the larger one,
where Banach uniqueness applies.  This does not by itself make an arbitrary
field-indexed family of certificates continuous.  To identify the canonical
choice with the local implicit branch near `A`, the branch must be shown to
remain in one common certified ball (for example from strict interior
membership), or a genuinely global uniqueness theorem must be supplied.
The presently proved weak membership `‖D_tilde(A)‖ ≤ ρ(A)` is not enough at a
boundary point and must not be silently treated as such.  The source-faithful
alternative, already used by the CMP102 equation-(80) correction, is to fix
the physical contour radii `r,s` and prove a two-field Lipschitz estimate for
the selected fixed points directly from the literal correction estimate.
That gives continuity of `A ↦ D_tilde(A)` without any regularity assumption
on the certificate family and is the preferred route for the CMP109
implicit-branch comparison.

Here the symbol `D₃` accepted by the abstract equation-(80) functional must
not be identified by notation alone with CMP109's
`D_tilde_3`.  Such an identification requires a theorem fixing the Taylor
order, the sparse insertion `h`, the sign, and the field coordinates.
Likewise, the determinant and `NearLog` developments used for the later
Gaussian covariance are not the Jacobian of the nonlinear CMP109 change of
variables.

Consequently the next code object cannot honestly be another arbitrary
`remainder : Y -> B -> R`.  It must be the literal finite, tagged family of
the eight CMP109 (2.12) species, together with the exact equality that its
domain regrouping is the fluctuation action in (1.41).  Only after that
equality may the seven Taylor remainders be added to the already constructed
Lemma-1 family and named `V''_k`.

The next acceptable bridge is:

```text
literal localized activity V_k(Y,B) of (1.41)
  -> source-faithful Q(Y,B) including the equation-(80) quadratic sector
  -> literal remainder V''_k(Y,B)
  -> estimate (1.36)
  -> Eq220 residual weights
  -> centered potential_bound.
```

No theorem should call a weakening leaf, an arbitrary radial Taylor residual,
or the residual of the currently installed bare summand `V''_k` without this
identity.
