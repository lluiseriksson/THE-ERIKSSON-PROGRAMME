# C6d source precision to Eq. (3.42) Dirichlet compression

Status: static design only.  No Lean/Lake result is claimed here.

## Exact next boundary

The sealed C6d object is the active-region operator

`cmp99Eq360C6dSourceBaselinePhysicalPrecision ... : ActiveGaugeZeroCochain Omega ->L ActiveGaugeZeroCochain Omega`.

`CMP99Eq342SourceLocalizedGreenCertificate`, however, fixes its Green to
`cmp99RegionalDirichletGreen Omega A ...`, where `A` is an operator on the
full ambient fine box.  The next brick must therefore construct the ambient
operator and prove that its Dirichlet compression is the literal C6d active
precision.  It must not accept that equality from the caller.

## Algebraic orientation lemma versus physical ambient producer

The canonical extension `Qprime.comp restrictZero` is sufficient to prove an
exact *compression identity* for the adjoint-square term.  It is not, by
itself, the physical ambient producer required by Eq. (3.42): outside
`Omega` its averaging mass vanishes, so coercivity of the local C6d precision
does not imply coercivity of the resulting ambient operator.  No Green or
Eq. (3.42) certificate may be generated from that algebraic extension alone.

The physical route must instead start from the complete source-generated
ambient tower, whose Laplacian and terminal `Qprime` act on the full carrier,
and prove that its Dirichlet compression is the literal C6d active precision.
The local-extension theorem is retained only as the orientation calculation
for the mass summand.

## Physical ambient ingredients

The source-localized Eq. (3.42) carrier has side
`cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)`, whereas the C6d
chain is parameterized by `Lfine * N'`.  The faithful specialization is

* `Lfine := L ^ (depth + 1)`,
* `N' := 2 * (K * Q)`, and
* retained-tower block factor `M := L`.

The equality between
`L^(depth+1) * (2*(K*Q))` and
`(K*L^(depth+1)) * (2*Q)` is an explicit carrier-reindexing obligation.  It
must be a named equivalence/dictionary, not a definitional identification.
The existing source-separated ambient dictionary already proves the relevant
side equality and exposes
`cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv`; reuse that arithmetic
and its distance theorem rather than introducing another opaque cast.  The
remaining geometry step is to transport the selected active region itself,
not merely the full-box field.

Let `E := extendZeroZeroCLM Omega` and `R0 := restrictZeroCLM Omega`.

* Ambient Laplacian: `cmp99GeneratedAmbientScaledCovariantLaplacian`
  on the same transformed physical background and spacing used by the C6d
  active Laplacian.  The existing theorem
  `cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression` supplies
  its exact compression.
* Active terminal average: the `Qprime` of
  `cmp99Eq360C6dSourceBaselineRetainedPhysicalTower`.
* Ambient terminal average: the terminal `Qprime` of the complete generated
  source tower.  A new exact theorem must identify its compression with the
  active terminal average.  `Qprime.comp R0` is only the right-hand side of
  that dictionary, not the ambient operator definition.
* Coefficient: the literal
  `cmp99Eq360C6dSourcePhysicalCountingCoefficient` already sealed in the C6d
  chain.
* Ambient precision: the literal full-carrier source precision built from the
  complete generated tower, with its independently proved coercivity.

## Required exact theorem

Prove, as an operator equality,

`cmp99SourceAmbientDirichletPrecision Omega ambientPrecision =
  cmp99Eq360C6dSourceBaselinePhysicalPrecision ...`.

The generic name is deliberate.  The older
`cmp99RegionalDirichletPrecision` is specialized to carriers of the form
`FinBox 4 (M * (2 * Q))`; the C6d source chain is first presented on
`FinBox 4 (L * N')`.  Solving that arithmetic shape by metavariable
inference would be a false dictionary.  The new compression keeps `d,N`
explicit and is definitionally the same restriction/precision/extension
sandwich.

The Laplacian summand follows from the existing compression theorem.  The
mass summand must first use the new full-tower/local-tower `Qprime`
dictionary and then the two named partial-isometry facts

* `activeGaugeRegion_restrictZero_comp_extendZero`, and
* `cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint`,

together with `ContinuousLinearMap.adjoint_comp`.  This is the orientation
gate: the proof must show the adjoint-square compression explicitly rather
than identify two maps because their types coincide.

## Green consequence

Only after the physical ambient coercivity and precision equality are both
available, prove equality between

* the canonical inverse of
  `cmp99SourceAmbientDirichletPrecision Omega ambientPrecision`, and
* `cmp99Eq360C6dSourceBaselinePhysicalGreen ...`

by inverse uniqueness from the two already-generated left/right inverse
identities.  Do not accept a Green equality as input.

## Non-claims

This brick alone does not prove any of the four Eq. (3.42) localized bounds,
does not produce uniform `B0` or `delta0`, does not attain window 15, does
not discharge rows 23--24, and does not move `20/41` or instantiate
`TermSource`.
## Hot validation queue after the retained cold gate

Published PRE-VALIDATION source head: `76bfe9c8` (with the generic-carrier
compression and coercivity bridge).  The hardened hot runner is pinned at
`56e06b46494301cb416266c81946f5388959b2a3` with SHA-256
`f06bd515b0d640ab813d8919723aa7e7f189fd0e9beea56467bc76383a8e8fba`.
It checks out that exact source object while preserving `.lake`, requires the
expected `2/5/3/3/6/6` audit headers and rejects axioms outside the standard
allowed trio.

Run stop-on-first-error in the retained Colab clone, preserving the already
materialized `.lake` graph:

1. `BalabanCMP99RegionalDirichletGaugePrecisionCompressionAudit`
2. `BalabanCMP99SourceActiveRegionFullCompanionAudit`
3. `BalabanCMP99SourceGeneratedMassCompressionAudit`
4. `BalabanCMP99SourceGeneratedPhysicalPrecisionCompressionAudit`
5. `BalabanCMP99SourceActiveRegionFullCompanionPrecisionAudit`
6. `BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecisionAudit`

The queue is diagnostic only.  A hot PASS does not remove PRE-VALIDATION and
does not move `20/41`; a later cold checkout must seal the exact corrected
SHA.  On failure, preserve the first real error and repair only that target.

## Physical specialization after the generic queue

Instantiate the full-companion ambient precision with the C6d
Laplacian-aware retained extension, the same closed radius chain and the
globally proved small-field bound.  Then use:

- the exact full-companion Dirichlet compression;
- `cmp99Eq360C6dSourceBaselinePrecision_eq_laplacianRetainedPrecision`;
- `cmp99Eq360C6dSourcePhysicalCountingCoefficient_eq_laplacianRetained`;
- the full-companion coercivity producer.

This produces one ambient precision whose Dirichlet compression is the
literal C6d baseline precision.  Only after that equality is compiled may the
canonical regional Green be installed and compared with the existing local
baseline Green by uniqueness of inverse.

## Source-separated carrier transport after the C6d Green

The C6d specialization first fixes
`N = L^(depth+1) * (2 * (K * Q))`.  The source-facing Eq. (3.42) carrier is
`(K * L^(depth+1)) * (2 * Q)`.  These are not definitionally the same
presentation.  Reuse the sealed equivalence
`cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth`, whose
forward direction is

`FinBox 4 ((K * L^(depth+1)) * (2*Q)) ≃
 FinBox 4 (L^(depth+1) * (2*(K*Q)))`.

The localized active region must be transported as a `Finset.map` through
the carrier equivalence, together with a named equivalence between the two
`ActiveGaugeRegion.Site` subtypes.  Reindex both the ambient precision and
the local Green through those explicit equivalences, and prove that
restriction/extension commute with the transport.  A cast of the full box
alone is insufficient: it would leave the localized region dictionary
implicit and would not justify the source-facing Dirichlet compression.

The orientation is fixed as follows.  Let `e` be the displayed equivalence,
let `OmegaSource` be the literal source-separated regional cell, and define
`OmegaC6d := cmp99ActiveGaugeRegionReindex e OmegaSource`.  The C6d ambient
producer is instantiated on `OmegaC6d`.  The source-facing ambient precision
is the conjugate of that producer by `e.symm`; its local compression is the
conjugate of the C6d local compression by the restricted site equivalence.
Neither `OmegaSource = reindex e.symm OmegaC6d` nor cancellation of the two
operator reindexings is definitional.  The former must cite
`cmp99ActiveGaugeRegionReindex_symm_reindex_eq`.  The scratch dictionary now
supplies the latter as `finitePiLpTypedKernelReindex_symm_reindex`, together
with the derived inverse-orientation compression theorem
`finitePiLpTypedKernelReindex_symm_sourceAmbientDirichletPrecision`.  Both
still await a compiler/audit verdict before the final Green equality can be
read on the source carrier.

The generic scratch dictionary now proves the two unconditional support
facts separately: ambient/local reindexing commutes with zero extension and
with restriction.  The inverse zero-extension statement is obtained by
applying the actual inverse equivalence and then reversing the resulting
equality; no `simp`-only identification of the two carriers is accepted.

## Finite cold-seal boundary after both hot queues

If and only if both retained-runtime queues emit literal PASS, promote the
three scratch source/audit pairs under their intended module names and add
the nine audit imports to `YangMillsCore`:

1. the six full-companion/compression pairs already present as
   PRE-VALIDATION source;
2. `BalabanCMP99ActiveGaugeRegionReindex`;
3. `BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision`;
4. `BalabanCMP99ActiveGaugeRegionReindexGreen`.

The cold queue therefore has exactly nine source/audit pairs and 46 expected
axiom readouts: `2+5+3+3+6+6+10+7+4`.  It must run from a fresh checkout with
no restored `.lake/build`, then build `YangMillsCore` in the same checkout.
PRE-VALIDATION is removed only in the later evidence-seal commit and without
changing any theorem statement.  A hot PASS, a green prefix, or the existence
of generated `.olean` files is not seal evidence.
