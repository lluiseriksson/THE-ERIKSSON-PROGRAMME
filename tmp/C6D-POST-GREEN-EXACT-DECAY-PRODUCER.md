# C6d post-Green exact decay producer boundary

Static design checkpoint only.  No Lean/Lake verdict is claimed here.

## Fixed endpoint

The operator to localize is not an arbitrary generated precision.  It is the
literal full-companion ambient precision used by C6d:

- `cmp99SourceActiveRegionFullCompanionPrecision` on the full active carrier;
- `cmp99SourceActiveRegionFullCompanionAmbientPrecision` after the named full-site reindex;
- `cmp99Eq360C6dSourceSeparatedAmbientPrecision` after the Step-7b carrier reindex;
- `cmp99Eq360C6dSourceSeparatedAmbientGreen` as the canonical regional inverse.

No equality to `cmp99SourceGeneratedPhysicalPrecision` is available or needed.

## Brick D1: full-companion precision localization

The reusable ingredients already in the tree are:

1. `CMP99SourceActiveRegionChain.generatedCountingMass_finiteRange`;
2. `CMP99SourceActiveRegionChain.generatedCountingMass_eq_QprimeMass`;
3. `cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one`;
4. `CMP99SourceActiveRegionChain.norm_weightedQprimeTower_Qprime_le_one`;
5. `norm_cmp99ActiveRegionSourceCovariantLaplacian_le`;
6. `finitePiLpKernelBound_of_opNorm_le`;
7. `finitePiLpTypedExponentialKernelBound_of_finiteRange`.

The missing geometric fact should be stated for an arbitrary typed chain, not
postulated for the full companion:

> `SameTerminalBlock source target` implies
> `finBoxDist target.1 source.1 <= M^depth - 1`.

A source-faithful proof route is to show by induction that equality of
`terminalSiteOfFine` gives equality of the coordinate quotients by `M^depth`,
then reuse the arithmetic window proof of
`finBoxDist_le_of_same_generatedTerminalBlock`.  This avoids identifying an
arbitrary full-companion chain definitionally with the iterated-lift chain.

With that lemma:

- the Qprime mass has range `M^depth - 1`;
- the sum with the covariant Laplacian has range `M^depth` (the same visible
  conservative radius convention as the existing generated precision);
- the operator norm is bounded by
  `4*d/spacing^2 + |fullCompanionCountingCoefficient|`;
- the entrywise kernel bound follows from the operator norm;
- finite range plus the kernel bound yields the ambient exponential precision
  bound at any chosen positive rate.

The first implementation unit should expose the following chain explicitly,
so later consumers cannot silently substitute the canonical iterated-lift
geometry for an arbitrary full companion:

1. `terminalSiteOfFine_val_eq_div_pow`;
2. `div_pow_eq_of_sameTerminalBlock`;
3. `sameTerminalBlock_finBoxDist_le`;
4. `generatedCountingMass_finiteRange_terminalBlock`;
5. `QprimeMass_finiteRange_terminalBlock`.

The arithmetic in item 3 is already present, source-for-source, in
`finBoxDist_le_of_same_generatedTerminalBlock`; the new content is the typed
chain quotient identity in items 1--2.  The scratch proof lives in
`tmp/BalabanCMP99SourceActiveRegionTerminalBlockDiameter.draft.lean` and is
not evidence until a Colab focal plus audit passes.

The Laplacian and mass budgets must remain separate until the literal sum is
formed.  Do not identify the full-companion counting coefficient with
`cmp99SourceGeneratedPhysicalMass`.

The exact full-companion precision budget is therefore the literal

`4*d/spacing^2 + |cmp99SourceActiveRegionFullCompanionCountingCoefficient ...|`.

The finite-range proof should follow the already compiled shape of
`cmp89SourceSeparatedFinePrefixPrecision_finiteRange`: derive the one-link
Laplacian zero and the terminal-block mass zero separately, unfold the literal
precision only at the endpoint, and close the sum.  This is a proof-template
reuse, not an operator identification.

## Brick D2: exact C6d Green decay

Implementation status: no D2 Green-decay theorem exists yet.  The current
post-Green promotion/gate covers D1 and the three named metric equalities
only.  A green D1/metric prefix must not be reported as D2 or as Eq. (3.42).
The source-facing D2 theorem is a separate subsequent brick that instantiates
the inverse theorem below for the literal C6d precision and canonical Green.
Its provisional module boundary is
`BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecay` plus its audit; this
name is not part of the D1/metric promotion manifest.

The corresponding scratch implementation now lives at
`tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecay.draft.lean` and its
audit.  It is deliberately outside the D1/metric manifest and remains
non-evidence.  The draft exposes three separate conclusions: the exact C6d
ambient precision bound, the source-separated precision bound after the
named metric reindex, and the canonical positive-depth Green bound obtained
from the generic inverse theorem.  The two scratch paths pass the lightweight
overlay text guard, but no Lean/Lake or axiom verdict is claimed.

Transport the D1 exponential precision bound through:

1. `cmp99SourceFullActiveRegionSiteEquiv`;
2. `cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv`.

Each transport needs a named `finBoxDist` preservation lemma.  Do not rely on
the word `reindex` or a definitional metric identification.

The first metric lemma is definitional on values because
`cmp99SourceFullActiveRegionSiteEquiv` is `Subtype.val`.  The Step-7b metric
lemma is not definitional: its site equivalence is the composite of the
source-separated full-site equivalence and
`cmp99GeneratedFineBoxOneBlockEquiv`.  Its proof should cite the existing
size-cast geometry (`finBoxDist_cast_size`, plus the already sealed
`finBoxDist_cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_symm`) and
expose the carrier-size equality by name.

Then apply the already sealed generic inverse theorem
`cmp99RegionalDirichletGreen_exponentialKernelBound` to the literal source
carrier.  Its canonical inverse is definitionally the regional Green and is
connected by the named theorem
`cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_ambient` to
`cmp99Eq360C6dSourceSeparatedAmbientGreen`.

The only analytic inputs at this endpoint are therefore:

- positivity and coercivity of the exact C6d ambient precision;
- the exact D1 exponential kernel bound;
- the existing volume-independent exponential site sum.

No free Green, regional precision, operator equality, or inverse identity is
allowed in the source-facing theorem.

### Static signature audit (2026-08-29)

The coercivity leg is already exact for the same operator and does not require
a new certificate.  On the source-separated carrier the consumer can cite

- `cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos`;
- `isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision`;
- `cmp99RegionalDirichletGreen_exponentialKernelBound`.

The last theorem consumes the ambient precision localization directly and
returns the canonical compressed Green with amplitude `2 / c` and rate
`finitePiLpExponentialInverseDecayRate A decay
  (cmp99OmegaSiteExpSumBound (decay / 4)) c`.
Thus D2 has no missing coercivity dictionary: the only missing input is the D1
exponential-kernel bound transported through the two named site equivalences.

The transport chain is now pinned to three named metric equalities:

1. `finBoxDist_cmp99SourceFullActiveRegionSiteEquiv`;
2. `finBoxDist_cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv`;
3. `finBoxDist_cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv`.

Their scratch statements live in
`tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientMetric.draft.lean`.  The third
is explicitly the composite of the first carrier change and the generated
one-block size cast; it is not to be replaced by an unnamed `rfl` in the final
producer.

The terminal-block diameter gate is a hard predecessor of D1.  A green focal
prefix alone is not sufficient: the diameter module and audit must pass, its
root must pass, and the exact pair must be selectively sealed before the
full-companion finite-range proof is promoted.

### Exact D2 instantiation (static, not compiler evidence)

The full-companion theorem must be instantiated with the literal C6d data,
not a parallel generated tower:

- `d := 4`, `M := L`;
- `rho := matrixSUNAdjointModel Nc`;
- `spacing := eta`;
- `epsilon := cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1`;
- `background := cmp99Eq360C6dSourceLaplacianRetainedExtension ...`;
- `chain := baselineRadiusBudget.toRadiusChain`;
- `fineSmall :=
  norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le ...`.

The proof sequence is fixed as follows.

1. Apply
   `cmp99SourceActiveRegionFullCompanionPrecision_exponentialKernelBound`
   to the active full companion with the data above.
2. Reindex by `cmp99SourceFullActiveRegionSiteEquiv 4 N` and rewrite the
   pulled-back metric only with
   `finBoxDist_cmp99SourceFullActiveRegionSiteEquiv`.
3. Unfold only the endpoint definition
   `cmp99Eq360C6dSourceAmbientBaselinePrecision`; do not unfold the retained
   tower or replace its counting coefficient.
4. Reindex by
   `cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv.symm` and rewrite the metric
   with `finBoxDist_cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv`.
5. Apply `cmp99RegionalDirichletGreen_exponentialKernelBound` using the exact
   source precision, the already compiled physical coercivity floor and its
   coercivity witness.
6. Rewrite the canonical regional inverse to
   `cmp99Eq360C6dSourceSeparatedAmbientGreen` only through
   `cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_ambient`.

This sequence leaves no caller-supplied precision, Green, inverse equality,
metric equality or coercivity certificate.  The only choices left to the
consumer are the positive CT rate and the physical C6d data already present
in the source constructor.

At positive depth the literal constants should remain visible as

- precision amplitude:
  `(4*d/spacing^2 + |fullCompanionCountingCoefficient|) * exp(rate*M^depth)`;
- Green amplitude: `2 / fullCompanionPhysicalCoercivity`;
- Green rate: the existing
  `finitePiLpExponentialInverseDecayRate` applied to those exact inputs.

This is a depth-dependent exact producer.  It must not be reported as the
uniform `B0/delta0` certificate until separate scale-uniform inequalities are
proved.

## Depth split

Positive depth consumes the C6d source Poincare coercivity producer.  Depth
zero must use the exact zero-depth Green branch already constructed; do not
smuggle `0 < depth` into an unrestricted Eq. (3.42) family.

The zero-depth D2 scratch is now separate at
`tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenDecayZeroDepth.draft.lean`
plus its audit.  It instantiates D1 at `depth = 0`, transports through the
full-carrier metric equivalence and applies the canonical inverse theorem
with the literal zero-depth counting coefficient as coercivity floor.  It is
outside the positive-depth D2 module and remains non-evidence until compiled.

## Downstream delimiter

D1+D2 produce value-kernel decay for the exact Green.  They do not yet produce
the four Eq. (3.42) actions (value, left derivative, right adjoint derivative,
covariant Laplacian), the common `[ell^2, ell, ell, 1]` scaling, or one uniform
`B0/delta0`.  Those remain the next source-facing action brick.

The scalar assembly pattern is already compiler-sealed in
`BalabanCMP96SourceSeparatedRegionalPrefixEq342Certificate`: it combines the
four literal action bounds through `cmp99Eq342CommonAmplitude` and preserves
the displayed `[ell^2, ell, ell, 1]` factors.  It is a template only, not the
C6d producer.  Its Green and region are the fixed
`cmp96SourceSeparatedRegionalCell`, whereas D2 produces the canonical inverse
on the selected `OmegaSource`.  The next brick must reinstantiate the four
actions on that exact transported Green; it may not restrict the old Green or
postulate equality of the two Dirichlet inverses.  The reusable downstream
lemmas are grouped in the existing value, left-derivative,
right-adjoint-derivative and Laplacian owner-decay modules, but each action
must be checked against the C6d carrier and terminal spacing before reuse.

The finite post-D2 chain is therefore:

1. convert the exact Green value decay from fine `finBoxDist` to the source
   owner/block metric and prove the block-localized value bound;
2. construct the source-carrier background dictionary for the literal C6d
   precision, then construct the literal left covariant derivative at the
   exact C6d spacing and
   prove its owner bound from the two endpoint values;
3. expand the literal right adjoint stencil and prove its owner bound without
   appealing to abstract adjoint symmetry;
4. construct the literal covariant Laplacian action and prove its owner bound
   from the signed forward/backward link terms;
5. assemble those four bounds into
   `CMP99Eq342RegionalGreenCertificate` with one common per-depth amplitude
   and rate and the exact `[ell^2, ell, ell, 1]` scale vector;
6. combine the positive- and zero-depth branches without imposing
   `0 < depth` on the family;
7. prove the separate scale-uniform inequalities that dominate the per-depth
   amplitude and rate by one physical `B0 > 0` and `delta0 > 0`.

Only item 7 is the uniform Eq. (3.42) endpoint.  Items 1--6 may be sealed and
reused, but none of them alone attains window 15 or changes `20/41`.

For item 1 the already sealed geometric bridge is
`cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary`:

`ell * ownerDist <= fineDist + 2 * (ell - 1)`.

It gives owner rate `ell * rate` and the explicit boundary payment used by
the existing fixed-cell proof.  The reusable geometry is source-wide, but
the old action theorem is not: it hard-codes
`cmp96SourceSeparatedRegionalCell` and its independently generated Green.
The C6d action brick must therefore rerun the action argument with D2's
canonical `OmegaSource` Green while citing this same bridge; it must not cite
the old theorem by pretending the two regions or inverses coincide.

There is also a normalization gate on that rerun.  Expanding the D2 Green
against coordinate probes and summing the one-owner fibre would pay its full
cardinality `ell^4`, whereas the printed value action pays `ell^2`.  The
accepted route is the already sealed arbitrary-input one:

1. instantiate
   `isCoerciveCLM_finitePiLpTiltConj_inverse_canonical` with D2's exact
   precision bound, exact coercivity and exact inverse;
2. feed that named tilted coercivity to
   `norm_finitePiLpInverse_apply_le_of_tilted_coercive`;
3. spend `norm_cmp99Eq342_sourceLocalizedTilt_le_sourceScale` exactly once.

Thus the action proof retains the counting-L2 norm until the final
`ell^2 * supNorm` conversion.  A coordinate-probe proof that produces
`ell^4` is valid auxiliary algebra but is not the physical item-1 producer.

Finally, D2 itself does not require a nonempty active carrier, while
`CMP99Eq342SourceLocalizedGreenCertificate` does.  The per-depth family
brick must therefore construct `Nonempty (ActiveGaugeRegion.Site
OmegaSource)` from the chosen physical source-region data.  Supplying a
free `root` merely relocates the obligation and is not the item-6 producer;
if the chosen region can be empty, that case must remain a separately named
branch rather than being silently excluded.

### Derived-action background gate (static audit, 2026-08-29)

The exact D2 Green alone does not identify the three derived actions in the
Eq. (3.42) record.  The source certificate fixes those actions to
`cmp99ActiveRegionSourceCovariantD0CLM` and
`cmp99ActiveRegionSourceCovariantLaplacian`, so their background and spacing
must be the same physical data used by the literal C6d precision.

On the pre-reindex carrier the named theorem
`cmp99RegionalDirichletPrecision_C6dSourceAmbientBaseline_eq` exposes the
regional precision as the source gauge precision whose Laplacian uses

- `(R.toCubeWitness C alpha1 hscale).transformedBackground`, and
- the literal C6d spacing `eta`.

After the Step-7b reindex, no theorem currently names the corresponding
source-carrier background or identifies the compressed precision with that
literal covariant Laplacian plus the transported retained `Qprime` mass.
Using an arbitrary `PhysicalGaugeBackground`, or silently substituting the
technical retained extension, would therefore construct a different action.

Before items 2--4 above, add one source-facing dictionary brick that:

1. defines the source-carrier background by the printed carrier transport
   (the existing `cmp99Eq389SourceSeparatedPhysicalBackground` is the
   intended value-level transport template);
2. proves the transport commutes with positive fine shifts/physical bonds;
3. proves the regional derivative and Laplacian are the reindexes of the
   literal pre-Step-7b operators; and
4. states the exact compressed-precision equality with the transported
   `Qprime` mass.

Only after this dictionary is named may the left, right-adjoint and
Laplacian actions cite the background and spacing.  This is a new explicit
prerequisite inside item 2, not a new terminal field and not progress on the
uniform `B0/delta0` endpoint.

The current Corollary-3.6 dictionary does not discharge this gate: it states
`OmegaPrime0.sites \subseteq C.carrier`, not the reverse inclusion.  Hence the
nonempty regular-cube carrier does not force the selected source region to be
nonempty.  At the type level the empty source region, empty head region and
their empty active-region chain satisfy that inclusion.  This is presently a
static countermodel, not compiler evidence; item 6 must either construct the
physical nonempty source subtype or seal the corresponding empty-region
no-go before choosing the family index.

### Exact action prefix (scratch only, 2026-08-29)

The value-to-action algebra has now been separated from the physical
specialization in six scratch modules:

- `BalabanCMP99Eq342LeftDerivativeFromValueBound` spends the two value
  endpoints and produces the exact `(1 + exp rate) / spacing` factor;
- `BalabanCMP99Eq342RightAdjointFromValueBound` expands the backward stencil,
  keeps the owner-radius-one ball `3^4 = 81` visible and produces `8 * 81 =
  648`, without abstract adjoint symmetry;
- `BalabanCMP99Eq342LaplacianFromLeftDerivativeBound` expands the four signed
  directions and cancels the remaining terminal `ell` explicitly;
- the three `BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen{LeftDerivative,
  RightAdjoint,Laplacian}` specializations fix the canonical D2 Green, the
  named transported C6d background and spacing `L^(depth+1) * eta`.

All six remain `SCRATCH ONLY`: none is compiler evidence, none changes
`20/41`, and none attains the uniform `B0/delta0` endpoint.  Their promotion
must remain downstream of a sealed exact value action and sealed physical
background dictionary.

The background dictionary itself is still incomplete in one precise place.
`cmp99Eq360C6dSourceSeparatedPhysicalBackground` fixes the value transport
and positive shift, but no current theorem identifies the source-reindexed
D2 compression with the literal

`cmp99SourceGaugePrecision (cmp99ActiveRegionSourceCovariantLaplacian ...
  cmp99Eq360C6dSourceSeparatedPhysicalBackground ... eta) Qprime b`.

That compressed-precision equality is the remaining semantic gate.  The
three action specializations construct literal operators, but they must not
be reported as actions of the D2 precision until this equality is named and
compiled.

The depth-zero normalization convention is now resolved statically.  The
named theorem `cmp99SourceAmbientDirichletPrecision_fullCompanion_eq`
identifies the compression with

`cmp99SourceGaugePrecision
  (cmp99ActiveRegionSourceCovariantLaplacian ... background spacing)
  Tregional.Qprime countingCoefficient`.

Thus the depth-zero parameter `spacing` is already the literal terminal
spacing consumed by the covariant Laplacian; the accompanying zero-depth
producer keeps the coefficient `spacing^(-2)`.  It must not be multiplied by
an additional RG block length.  The current generic two-endpoint action
lemma hard-codes terminal spacing as `ell * spacing`, so it is not yet a
source-faithful zero-depth consumer.  The next reusable interface should
accept an explicit `terminalSpacing`, with positive depth instantiated by
`L^(depth+1) * eta` and depth zero by `spacing`.  No zero-depth derived-action
scratch is claimed until that explicit-spacing interface is compiled.

Three scratch adapters now make that interface explicit without changing any
compiled claim:

- `BalabanCMP99Eq342LeftDerivativeAtTerminalSpacing`;
- `BalabanCMP99Eq342RightAdjointAtTerminalSpacing`;
- `BalabanCMP99Eq342LaplacianAtTerminalSpacing`.

Each adapter rewrites the older auxiliary scale as
`terminalSpacing / ell`.  This is algebra only: the positive-depth and
depth-zero physical specializations, their exact amplitudes and all three
audits remain open until a Colab queue promotes and compiles them.  In
particular, the adapters do not identify the two physical spacing conventions
and do not alter `20/41`.

`BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthActions` is the
corresponding scratch consumer.  It fixes the literal depth-zero spacing to
`spacing` in all three operators and keeps the residual `L` powers visible in
the action amplitudes.  It remains uncompiled and is not part of the current
Green-owner promotion until its adapters and the zero-depth value action have
passed together.
