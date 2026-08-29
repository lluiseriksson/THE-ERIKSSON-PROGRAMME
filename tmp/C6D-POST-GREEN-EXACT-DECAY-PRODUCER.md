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

## Downstream delimiter

D1+D2 produce value-kernel decay for the exact Green.  They do not yet produce
the four Eq. (3.42) actions (value, left derivative, right adjoint derivative,
covariant Laplacian), the common `[ell^2, ell, ell, 1]` scaling, or one uniform
`B0/delta0`.  Those remain the next source-facing action brick.
