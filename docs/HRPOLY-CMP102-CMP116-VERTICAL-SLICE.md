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
| `contour` | **non-circular constructor exists**: `CMP116Eq214PhysicalContourDensity.ofSourcePi4RestrictedPhysicalContour` starts from a private neutral dependent shell and overwrites the potential, bond field, and full restricted complex Gaussian from physical producers; no inhabited contour density is an input |
| `source` | physical Gamma/operator ingredients and their complex-contour installation exist; source faithfulness still depends on the literal indexed potential/remainder ledger supplied to the constructor |
| `domainMetric`, `domainCard`, `domainSupport` | the combined direct/native dictionary is explicit and its nonemptiness/subset laws are proved; installation in a source-specific `PreEq136` inhabitant remains pending |
| Cauchy-radius identities | generic CMP116 formulas exist and the target identities are explicit fields of `PreEq136`; their source-specific installation is still pending |
| positivity/smallness scalars | many scalar lemmas exist; no complete source record |
| `outer_bound`, `inner_bound`, `source_bound` | generated in the centered-conditioned physical contour lane from the covariance/contour producers, subject to the named contraction and scalar windows; they are not consequences of equation (80) alone |
| contour `potential` summand | **combined partial ledger constructed**: the direct Eq-80 fixed quadratic core and cubic Taylor residual are literal, and direct (1.36) is derived from the physical third-jet/walk producers; the native Lemma-1 residual is separately indexed and carries its named restricted source certificate; installation in a complete pre-source and the remaining printed species are open |
| `interaction_bound` | **open at installation level**: the direct (1.36) and combined Eq-219/rooted ledgers now have producers, while the native analytic (1.36) remains the explicit CMP109 certificate; the final centered AE potential bound and scalar interaction budget have not yet been assembled into `PreEq136` |
| `domain_nonempty`, `domain_subset` | discharged for the combined direct/native dictionary, with the centered region enlarged rather than silently dropping boundary domains |
| `rooted_residual` | direct and native producers are combined under one explicit root bound; installation remains pending |
| `volume_budget` | an exact combined physical volume rate/cost producer exists; the remaining scalar target and installation stay visible |

Therefore:

```text
physical CMP116Eq226PhysicalContourTermSource constructed: 0
terminal boundary objects discharged from CMP102:          0 / 5
terminal theorem instantiated nontrivially:                 0
```

### Progress denominator for the centered-conditioned constructor

The raw `PreEq136` structure contains data, choices, definitional
normalizations, and proof fields, so neither its raw field count nor the
existence of a constructor measures whether the record is inhabited.  The
consumer-facing audit groups the proof debt into the **41 obligations before
equation (1.36)** and treats equation (1.36) separately.  The live metric is
therefore

```text
PreEq136 obligations with a source-specific producer / 41.
```

A field counts only when its producer is independent of an already inhabited
`PreEq136` record and does not receive the same conclusion under another
name.  In particular,
`cmp116Eq226CenteredConditionedCombinedPartialTermSourceOfPreEq136` is a real
constructor from `PreEq136`, but not an inhabitant of `PreEq136`; it does not
by itself change this numerator.  The numerator must be recomputed from the
field-by-field producer map after every interface change, rather than inferred
from the number of modules or successful builds.

### Current producer map for `PreEq136`

The following table is the live source-facing map.  A theorem marked
"producer" has the correct conclusion independently of an inhabited
`PreEq136`; "installer pending" means that the theorem has not yet been used
to construct the corresponding field of a source-specific pre-record.
Unvalidated files do not enter the numerical progress numerator.  The focal
queue through the combined constructor was materialized at source checkpoint
`134a21f0` in one fresh Colab Pro+ clone; all focal targets, `YangMillsCore`,
and the full oracle exited zero.  The downloaded evidence archive has SHA-256
`589769BC64D24493B0F68F5B0458DB017258919B32C265D8C83FA327487233EC`.
The later source-specific assembler gate was run from a fresh Colab clone at
source checkpoint `7fb235a3c86d3077b3d978a24a5623cd562eef9c`: the focal build
completed successfully with 8975 jobs, `YangMillsCore` completed successfully
with 10348 jobs, and the full oracle exited zero.  Its transcript has SHA-256
`5c432c9a7cfa7c1bb81fa3cc8ec25d66e2e07d758b9089f887e0f6bd07670999`.
The interacting-precision source was then validated from one fresh Colab
CPU/high-RAM clone at source checkpoint
`5b061eb968885f5d724dc3b9226ee593ddc5d0db`: the focal build completed with
8977 jobs, `YangMillsCore` completed with 10350 jobs, and the full oracle
exited zero.  The focal, root, and oracle log hashes are respectively
`b54bc45b29b15b41c92f27dfc81ac7eec15c1754b93d3a29d46f7dc836c7a7a1`,
`7afa58d2c5771c975e81e35e2b6d6969d6679b18eba717c3f0b432f6140d390f`,
and `511a0a43775e8d75ab5f17cd8114e02a3eaa4cbb0f07433a4179d5069f9d7d34`.

| Obligation group | Source status |
|---|---|
| non-circular contour density | producer compiled: `ofSourcePi4RestrictedPhysicalContour`; the literal direct/native potential adapter still supplies its inputs |
| combined `total` / `residual` ledger | exact direct/native definitions and sum identities compiled |
| `domainMetric`, `domainCard`, `domainSupport` | canonical appended dictionary compiled |
| `domain_nonempty`, `domain_subset`, `domainMetric_nonneg` | producers compiled for the enlarged centered region |
| `rooted_residual`, `rootBound_nonneg` | direct/native combined producers compiled; terminal installer pending |
| `volume_budget` | exact combined physical volume-rate producer compiled; scalar target remains visible |
| equation (1.43) | combined physical producer and source-specific terminal-field adapter compiled; neither accepts a free Hessian estimate |
| equation (1.36) | direct sector derived from CMP102 jets and walks; native sector is the named positive, nonempty-small-field CMP109 certificate; the combined finalizer is compiled but still requires a `PreEq136` inhabitant |
| literal `kernelSupport`, `metric_budget` | source definitions and proofs compiled in the clean focal queue |
| `smooth`, `hessian_zero_off_support` | source proofs compiled from the projected direct core and zero native core |
| covariance range (`sourceRange_bound`, `finiteRange`) | literal interacting-precision producer compiled and installed |
| covariance/parametrix contractions and contour bounds | remain explicit physical producer inputs; no source-specific pre-record yet assembles all of them |
| conditioned covariance lower certificate | mandatory nondegeneracy input; it must not be synthesized by choosing a degenerate Gaussian root |
| scalar windows (`shell`, contour/Neumann, root, outer, interaction, volume) | individually named; the compiled combined ledger pins `alpha` to the canonical sum of the literal potential rate, literal bilateral R2 rate, and `gamma`, but this normalization does not discharge `root_small` or `outer_small`; a single source-specific compatibility witness covering the live set remains open |

Under the 41-obligation grouping above, the current auditable numerator is

```text
18 / 41
```

The eighteen independently produced entries are: the non-circular contour
density; literal `total` and `residual`; literal `domainMetric`, `domainCard`,
and `domainSupport`; `domain_nonempty`, `domain_subset`, and
`domainMetric_nonneg`; `rooted_residual` and `rootBound_nonneg`;
`volume_budget`; equation `(1.43)`; literal `kernelSupport`; `metric_budget`;
`smooth`; `hessian_zero_off_support`; and the literal covariance-range
package (`sourceRange_bound`, `finiteRange`).  Equation `(1.36)` is
deliberately outside this denominator.  The canonical `E0`, `threshold`, and
`alpha` equalities are not added to the numerator while their only terminal
use still passes through an already inhabited `PreEq136` record.

The complementary `23 / 41` is the following explicit audit list.  These are
**obligation groups**, not raw Lean fields: a group may contain the sign
conditions and structural certificates which have to be inhabited together.
"Partial producer" means that the physical expression or a propagation
theorem already exists, but at least one source-facing hypothesis or joint
smallness inequality is still an input.  It does not increase the 18/41
numerator.

The `terminal demand` column prevents two different questions from being
confused.  `exact` means an identity, inclusion, or certificate for the
literal object; `positive/finite` means that the terminal type does not ask
for an optimal constant, although a poor witness can still fail a later
smallness inequality; `threshold` means a genuine strict or joint numerical
window; and `source bound` means an estimate on a literal physical map or
walk, not merely the existence of some scalar.  In particular, no remaining
field literally asks for the *fine* CMP99 constant.  Missing primary papers
can still be needed to prove that the physical witnesses land inside the
threshold windows.

The final column is a routing classification, not a proof claim.  `tree`
means that no missing primary source is currently known to be essential;
`corpus` means that the needed source statement is present in the acquired
primary corpus but still has to be formalized; and `absent` records a paper
whose primary text is not currently available.  Mixed entries retain every
applicable label.

| # | Remaining obligation group | Terminal demand | Current status | Current route |
|---:|---|---|---|---|
| 2 | coercivity package (`coercivity_pos`, `mass_pos`, `K_coercive`) | positive witness on the literal `K`; no optimal coercivity constant is requested | partial: the surviving coercivity constant and `K_coercive` are produced and installed; `mass_pos` remains an input.  This is the visible Poincare/Combes--Thomas wall | tree; CMP99 [14] may sharpen the physical constants but is not required by the terminal type |
| 3 | patched inverse contraction (`patchedDefect_small`) | **threshold** on the literal patched defect | partial producer; the defect is literal, the strict inequality is open | tree; source estimates may be needed to cross the threshold |
| 4 | weighted patched-parametrix certificate (`patchCertificate`) | **source bound**: two factorwise weighted-kernel estimates, not a mere sign | partial producer; the certificate and a constructor from physical patch data, range, row sums, and tilt budget exist; physical inputs remain open | tree + absent: CMP99 [14] for source-faithful physical inputs, not for a uniquely fine terminal constant |
| 5 | propagation geometry (`distance_triangle`, `exponential_row_bound`) | exact triangle law plus any finite explicit row majorant; its size matters downstream | partial producer; the metric is fixed, the uniform row budget is still supplied | tree; CMP99/CMP102 can improve the useful physical majorant but the type does not demand an optimum |
| 6 | contour carrier inside `sigmaZero` (`carrier_subset_sigmaZero`) | **exact** inclusion | open installation proof | tree |
| 7 | contour carrier inside the combined centered region (`carrier_subset_Z0`) | **exact** inclusion | open installation proof | tree |
| 8 | combined centered region inside the chosen outer region (`Z0_subset_Z`) | **exact** inclusion | open installation proof; enlargement cost stays visible | tree |
| 9 | contour adjacency budget (`degree_bound`, `one_le_Delta`) | any finite degree majorant; larger `Delta` worsens group 11 | partial combinatorial producer | tree |
| 10 | contour radius envelope (`radius_nonneg`, `radius_cap`) | any nonnegative envelope; larger radius worsens group 11 | open scalar/geometric envelope | tree |
| 11 | contour contraction package (`Ahead_nonneg`, `rho_nonneg`, `rate_pos`, `shell_small`, `contour_series_small`, `neumann_small`, `neumann_transpose_small`) | **joint threshold** package | partial physical producer; joint contraction is open | tree + corpus: CMP116 |
| 12a | conditioned Gaussian root (`conditionedRoot`) | **exact** square-root/support certificate | partial covariance producer; the abstract matrix square-root certificate is present | tree |
| 12b | **localized covariance compression bridge** | **exact** compression/root identification plus quantitative upper/lower bounds | **upper and lower analytic bridges verified** in a fresh Colab clone at `460c05e5`.  The lower construction uses the deliberately coarse constant `coercivityConstant / precisionUpperBound^2`.  A geometric proof that the localized carrier is nonempty is still required, so this does not change `18/41`. | tree; CMP99 [14] can sharpen the lower constant but is not required by the terminal type |
| 13 | strict conditioned covariance lower certificate (`conditionedCovariance_nondegenerate`) | **some positive** lower bound plus carrier nonemptiness; no optimal eigenvalue bound | analytic producer compiler-verified at `460c05e5`; only the geometric `S.Nonempty` producer remains open before installation | tree, downstream of groups 2 and 12b |
| 14 | sigma Cauchy-radius normalization (`deltaRadius_eq`) | **exact** equality against the installed contour | open equality against the installed base contour | tree |
| 15 | cardinality normalization (`normalizedGap`) | **exact** equality in the chosen convention | open equality in the source convention | tree |
| 16 | tau Cauchy-radius normalization (`yRadius_eq`) | **exact** equality against the combined metric | open equality against the combined domain metric | tree |
| 17 | outer-series window (`qBound_nonneg`, `qBound_lt_one`) | **threshold** `0 <= qBound < 1` | open joint scalar window | tree + corpus: CMP116 |
| 18 | source-amplitude hierarchy (`E0Direct_nonneg`, `epsilon1_pos`, `epsilon1_le_one`, `C1_pos`, `alpha4_pos`, `C3_nonneg`, `C3_le`, `amplitude_nonneg`) | signs and ordered **source bounds**; faithfulness fixes the printed `C3` formula | partial; formulas are fixed, joint source inequalities are open | tree + corpus: CMP116 |
| 19 | block/exponent hierarchy (`one_le_M`, `eight_le_q`, `one_lt_kappa1`, `source_budget`) | **source threshold** hierarchy | partial source-facing scalar regime | tree + corpus: CMP116 |
| 20 | direct third-jet envelope (`hD`, `hD₃`, `hV₀`, `hC`, `hRjet`, `hsourceJet`, `sourceJetBound_nonneg`) | **source bounds** on the literal physical maps | partial CMP102 producer; the printed component estimates remain hypotheses | tree + absent: CMP102/[15] source text genuinely bites here |
| 21 | walk factorization and Eq.-(1.43) budget (`cardRatio_nonneg`, `metricRatio_nonneg`, `summationRatio_nonneg`, `walk_split`, both decay rates, `cardDecay`, `metricDecay`, `walk_small`, `eq143_budget`) | **source bounds plus thresholds** on the literal walk ratios | partial producer; these inputs already feed the verified Eq.-(1.43) conclusion | tree + corpus: CMP116; source provenance still audited field by field |
| 22 | residual/rooted animal windows (`residual_rate_nonneg`, `rooted_rate_nonneg`, `animal_small`, `rooted_animal_small`) | **threshold** windows | partial combinatorial producer; the joint scalar witness is open | tree + corpus: CMP116 + absent: Cammarota [26] for the deferred Mayer input |
| 23 | canonical interaction/root stability (`alpha_pos`, `gamma_nonneg`, `root_small`) | **threshold** on the physically linked root | open scalar wall at the least admissible `alpha`; its one-variable reduction is proved, but it is not physically instantiable before bridge 12b and group 13 | tree, downstream of groups 2, 12b, and 13 |
| 24 | outer Gaussian stability (`outer_small`) | **threshold** coupled to the same `alpha` and root | open scalar wall; its one-variable reduction is proved, but it is not physically instantiable before bridge 12b and group 13 | tree, downstream of groups 2, 12b, and 13 |

This type-level audit falsifies the strong version of the predicted
`30--34/41` plateau.  Groups 2, 5, 9, 10, and 13 do not require the fine
constant from an absent paper; deliberately coarse positive or finite
witnesses are admissible.  It does **not** prove that arbitrary coarse
witnesses close the regime: their sizes feed the strict windows in groups 3,
11, 17, 22, 23, and 24.  The papers can therefore remain quantitatively
important without being logically required by the corresponding field type.

For group 13, `domain_nonempty` and `domain_subset` do not by themselves
produce the required localized-coordinate carrier witness.  The combined
domain index may be empty, subset containment creates no interior bond, and
the selected physical bond carrier `P` may itself be empty.  Conversely, an
explicit `P.Nonempty` is sufficient: the existing
`coordEquiv_symm_mem_physicalLocalizedCoordinates_localizationCore` theorem
places every Lie coordinate of a selected bond in the localization core, and
the source-coordinate dictionary transports that witness to
`cmp116SourcePhysicalLocalizedCoordinates`.  Carrier nonemptiness is thus a
small but genuine geometric obligation, not a consequence of the two domain
fields already counted.

Elaboration failures are triaged separately from project mathematics.  If the
first error occurs in a proof step whose statement and diagnostic mention no
project declaration, variants are tested first in a minimal file importing
only the smallest relevant Mathlib module.  This applies not only to instance
synthesis, but also to generic algebraic rewrites, matrix identities,
orientation of inequalities, and normalization of norms or inner products.
The full hRpoly target is retried only after that reproducer elaborates.  This
keeps a generic Mathlib experiment from consuming a fresh full-project Colab
bootstrap for every candidate proof.

Thus `18/41 -> 41/41` is the route to the first source-specific
`TermSource` **conditional on the named Lemma-1 certificate**.  Proving the
analytic Lemma-1 instance of equation (1.36) is a separate step which removes
that condition; it is not one of these twenty-three remaining pre-(1.36)
groups.  Row 12b is shown separately because it is a genuine source-facing
construction gate before groups 23--24, even though it is not an additional
raw `PreEq136` field and therefore does not change the formal denominator 41.

The two pending Hessian fields are deliberately not read back from the input
record.  Their ledger theorems rewrite only `total`, `residual`, and
`kernelSupport` to literal source objects.  In the native branch the zero
Hessian is an arithmetic consequence of installing the same literal native
residual in `total` and `residual`; this checks the assembled ledger, not an
independent CMP109 claim that the native activity has no quadratic part.

### Contract of the next source-specific pre-record assembler

The next constructor must stop accepting the following fields from an
already inhabited `PreEq136` record.  They are fixed by the literal combined
ledger or have source-facing producers:

```text
literal data fixed by the ledger:
  total, residual
  domainMetric, domainCard, domainSupport, kernelSupport
  E0 = E0Direct + lemma1.E0
  threshold = epsilon1 / gk
  alpha = potentialRate + r2Rate + gamma

proof fields generated from those data:
  smooth
  domainMetric_nonneg
  metric_budget
  hessian_zero_off_support
  eq143
  interaction_budget                  -- normalization only
  domain_nonempty, domain_subset
  rootBound_nonneg, rooted_residual
  volume_budget                       -- under its explicit scalar target
```

Until that assembler exists, adding equalities to
`CMP116CenteredConditionedCombinedEq80LedgerIdentification` strengthens the
identified branch but does not reduce the input telescope: the caller still
supplies an inhabited `PreEq136`, including the stored copies of the proof
fields.  In particular the new canonical `alpha` equality is not counted as
progress in the live numerator.  Its purpose is to prevent a later assembler
from choosing post-hoc slack while leaving the two genuine scalar walls

```text
(potentialRate + r2Rate + gamma) * ||conditionedRoot||^2 < 1,
outer_small at the same canonical alpha
```

visible and jointly testable.

The implementation of this contract is now validated in
`BalabanCMP116Eq226CenteredConditionedCombinedSourcePreEq136.lean`.  It splits
raw source data from the surviving physical proof inputs and constructs the
literal combined `PreEq136` without accepting an inhabited pre-record or any
of the seventeen generated conclusions.  Its source and audit passed the
fresh-Colab focal/root/oracle gate at checkpoint `7fb235a3`; this validation
does not increase the then-live 17/41 numerator, because the assembler installs those
seventeen existing producers rather than creating new ones.

The fields that remain inputs to that future assembler are the physical
contour density and geometry, covariance/coercivity/finite-range data,
patched-parametrix and contour certificates, conditioned covariance and its
strict lower certificate, component jets and random-walk budgets for the
direct equation-(80) sector, the named Lemma-1 certificate, and the live
scalar compatibility inequalities.  Repackaging those inputs is not itself
a physical discharge.

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

### Cardinality and metric conventions

Every cardinality or distance in this slice carries its lattice unit.  The
following table is normative for new interfaces and proofs:

| Lean symbol | Unit / convention | Exact relation or warning |
|---|---|---|
| `CMP116LocalizationDomain.sourceCard` | fine-lattice sites in the physical carrier | `sourceCard = M^4 * blocks.card` |
| `CMP116LocalizationDomain.blocks.card` | number of coarse `M`-blocks | this already represents the printed normalized quantity `M^-4 * |Y|` |
| `cmp116Eq80Lemma1CombinedDomainCard` | branch-local normalized block count | direct branch is the `M`-block count; native branch is the literal `2`-block count before coarsifying its support |
| `cmp116CubeEdgeTreeMetric Y` | number of coarse cube edges in a shortest carrier, on the lattice native to `Y` | it is already a normalized combinatorial length; it is not a fine-site distance |
| `cmp116Eq80Lemma1CombinedDomainMetric` | branch-local native tree metric | direct and native metrics retain their own block lattices; the native metric is not recomputed after support coarsification |
| `physicalBondDist b b'` | fine-lattice Chebyshev bond distance, including the direction coordinate | comparison with block counts costs an explicit factor of `M`, e.g. `physicalBondDist <= 4*M*blocks.card` |

Consequently, an interface whose `domainCard` is `blocks.card` must never
multiply that value by another `M^-4`.  The printed prefactor `alpha4*M^-4`
is a different amplitude normalization and remains present.  The two
conventions are kept distinct in every equation-(1.43)/(2.19) budget.

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
assumption.  The source-jet inputs and the scalar comparison with the printed
constants `C3`, `epsilon1`, `C2`, and `kappa1` are now composed physically in
`BalabanCMP102Eq80CouplingScaledEq143SourceMetric.lean`.

That scalar comparison is now isolated in
`BalabanCMP102Eq80PhysicalDomainFTCEq143SourceMetric.lean`.  It selects

```text
kappaCard   = (kappa1 - 1) / 2
kappaMetric = (kappa1 - 1) / 8
```

Here `Y.blocks.card` is already the normalized source cardinality
`Msource^(-4) * |Y|`; multiplying it by another `Msource^(-4)` would count
the source normalization twice.  The two choices remove every dependence on
`Y` from the remaining producer budget.
The reconstruction offsets `exp(kappaCard * 10000)` and
`exp(kappaMetric * 10000)` remain visible in that budget.  They are fixed
smallness thresholds on the walk ratios, not additional decay in the domain
metric.

`BalabanCMP102Eq80PhysicalIndexedEq143.lean` closes the remaining indexed
bridge.  It identifies the literal direct core `total - residual` exactly
with one half of the projected coupling-scaled Hessian at zero.  The exact
Hessian formula for a quadratic diagonal and
`norm_physicalBondProjection_le_one_anyVolume` then transport the physical
CMP102 producer with constant one.  The resulting endpoint derives (1.43)
from the component jets, walk ratios, contour cap, and coupled producer
budget; it takes neither a pointwise Hessian bound nor (1.43) as an input.

`BalabanCMP102Eq80PhysicalCombinedEq143.lean` then installs that producer on
the canonical disjoint direct/native ledger.  The direct branch reduces to
the indexed theorem above, while the native Lemma-1 branch has identically
zero quadratic core because its literal residual occurs in both `total` and
`residual`.  Thus the combined terminal `eq143` obligation is discharged
without a native Hessian hypothesis.

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
radial operator can become Balaban's complete source `Q(Y,B)` only after the
remaining source-domain assembly; the indexed direct matrix-element estimate
(1.43) itself is now proved by the bridge above.

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

The scalar wall is now visible in the terminal data.  Write
`A = potentialRate + r2Rate + gamma` and let `R` be the real matrix of the
terminal root.  The first inequality is literally

```text
A * ||R||^2 < 1.
```

The currently installed interacting-precision package does **not** yet imply
this inequality.  It constructs `K`, its exact inverse
`interactingCovariance`, and the positive constant

```text
c = min(1,a) / CP - interacting defect budget.
```

However, `CMP116CenteredConditionedCombinedSourceData.root` remains an
independent endomorphism.  Its `conditionedRoot` field proves only that the
finite matrix of this root is symmetric, carried by the localized
coordinates, and squares to the separately supplied `conditionedCovariance`.
No field identifies that covariance with a localized compression of
`interactingCovariance`, or the root with the positive square root of that
compression.  Therefore substituting
`||R||^2 <= c^-1` at the present interface would be an unjustified
identification.

The missing source-facing bridge can be stated without ambiguity: construct
the finite conditioned covariance as the localized coordinate compression of
the literal interacting covariance, take its positive square root, and prove
the existing conditioned-root and nondegeneracy certificates.  Equivalently,
a physical localized covariance-root certificate may first supply the global
root data, followed by the compression theorem.  The required norm chain is

```text
||R||^2 = ||conditionedCovariance||
        <= ||interactingCovariance||
        <= c^-1.
```

The first equality and the scalar consequences of the last inequality are
now isolated in `BalabanCMP116ConditionedRootScalarWall.lean`.  It was
validated in one fresh Colab CPU/high-RAM clone at source checkpoint
`4cf34623cf6096f89653cd9fb1c3dc848a7e9294`: the focal build completed with
8202 jobs, the audit declarations used exactly
`[propext, Classical.choice, Quot.sound]`, and `YangMillsCore` completed with
10352 jobs.  The complete pipeline exited zero after 7531 seconds; its log
has SHA-256
`8c7703a5823ff269b28813761a924311129721225c6d108be303da9b8fab55d8`.
In particular, the module derives both normalized terminal smallness
conditions from the single visible input

```text
||conditionedCovariance|| <= c^-1.
```

The physical upper bridge is now supplied by
`BalabanCMP116InteractingConditionedCovariance.lean`.  Starting from the
literal interacting precision, it constructs the canonical covariance
matrix, compresses it to the localized coordinates, reconstructs its positive
spectral root as a physical endomorphism, and proves both the exact root
certificate and

```text
||conditionedCovariance|| <= c^-1.
```

This specialization was validated in one fresh Colab CPU/high-RAM clone at
source checkpoint `141cbfe11c8566c4e917c460e86a34dfe47238dc`.
The focal target completed with 8474 jobs in 1231.383 seconds; its eleven
audit declarations use exactly `[propext, Classical.choice, Quot.sound]`.
The complete stop-on-first-error run exited zero after 1406.008 seconds and
produced evidence SHA-256
`5011a4bb91b2e489ffb74686537794a3e43318994c449c8b3a8a805a71092be3`.

This still does **not** increase the `18/41` producer count.  The strict lower
nondegeneracy certificate is a separate obligation.  At checkpoint
`460c05e5ac5e00536805c087526b15b9dc157dbb`, the same physical module was
extended and compiler-verified with the deliberately robust lower estimate

```text
(coercivityConstant / precisionUpperBound^2) * ||v||^2
  <= <v, conditionedCovariance v>.
```

The associated terminal lower certificate is therefore analytic, not
source-pending.  Its installation still requires an explicit proof that the
localized coordinate carrier is nonempty; `domain_nonempty` and
`domain_subset` do not imply that fact.  Keeping row 12b separate prevents
groups 23--24 from being misread as scalar arithmetic that is already
physically instantiable.

After that bridge, and assuming the displayed rates are nonnegative, the
first wall has the clean sufficient condition

```text
A < c.
```

The second wall is the literal terminal inequality

```text
2 * (outerRate + |sourceCoefficient(R,A) * sourceRate|) <= qBound,
qBound < 1,
sourceCoefficient(R,A) = ||R||^2 / (2 * (1 - A * ||R||^2)).
```

If `sourceRate >= 0`, the same root certificate and `0 <= A < c` reduce it to
the sufficient scalar condition

```text
2 * outerRate + sourceRate / (c - A) <= qBound < 1.
```

Thus the wall is now a two-stage frontier rather than a completed numerical
test: first identify the terminal Gaussian root with the coercive inverse
square root; then test the two displayed inequalities jointly.  In four
dimensions `CP` scales like the square of the fixed block ratio, not the
ambient volume, so that dependence remains visible in `c`.

These smallness conditions must eventually be witnessed **jointly**.  They
must not be audited by assigning arbitrary numerical values to norms of
operators that are themselves part of the physical producer.  The current
terminal record separates as follows:

```text
pure scalar once the displayed parameters are fixed:
  shell_small
  contour_series_small

scalar inequalities with physical quantities still inside:
  neumann_small                 (contains ||K||)
  neumann_transpose_small       (contains ||K^T||)
  root_small                    (contains the terminal root matrix norm)
  outer_small                   (contains the physical R1/R3 budgets)

genuinely operator-valued obligations:
  patchedDefect_small
  the pending pivot contraction ||K_U - I|| < 1.
```

Thus a numerical witness for freely named values such as `||K||`,
`||root||`, or the patched defect would prove only compatibility of an
abstract envelope, not nonvacuity of the physical record.  The honest
eventual witness must consist of:

1. physical upper-bound theorems tying every scalar envelope to the literal
   operators;
2. one simultaneous scalar specialization satisfying all resulting
   inequalities.

At the level of the explicit final contour bound, increasing `rate` does not
create the suspected direct conflict between `shell_small` and the Neumann
conditions: `cmp99PhysicalBondGeometricRowSum 4 rate` decreases toward its
finite shell prefactor as `rate` increases.  A real tension may nevertheless
re-enter through the producer of `CMP99PhysicalPatchWeightedCertificate`,
where the same rate is constrained by the residual rates
`kappa - sigma - mu` and `kappa - 3*sigma - mu` and by the tilted coercivity
budget.  Those producer constraints must be included in the eventual joint
witness.

The analytic denominator is three, not four:

```text
potential_bound : open
r2_bound        : open
cutoff_energy_bound installed in the centered terminal record : open
```

`interaction_budget` is only the optimal normalization
`alpha = potentialRate + r2Rate + gamma`; it is not counted as an analytic
discharge.  The combined ledger now records that equality using the literal
terminal potential and bilateral R2 rates.  This currently strengthens the
ledger presented to the already inhabited `PreEq136` record; it removes no
constructor input until a later source-specific assembler omits the stored
budget and rebuilds it from the equality.  At that point `alpha_nonneg` must
be regenerated from componentwise rate signs, while the strict
`root_small` and physical `outer_small` inequalities remain genuine source
obligations.  No complete centered conditioned `TermSource` has yet been
constructed, and neither `hraw` nor `hRpoly` is proved.

## Equation-(80), the indexed cutoff estimate, and the missing residual

The canonical Pi4 indexing and the one-domain cutoff estimate are available,
but the latter has not been identified with Balaban's `V''_k`.

The target object is now fixed as the **complete physical activity for one
domain**, not an isolated fine-head/tail summand.  The following chain still
feeds that target directly:

```text
BalabanCMP102Eq80GlobalPotential
BalabanCMP102Eq80PhysicalDomainFTCThirdFieldSourceMetricBound
BalabanCMP102Eq80CouplingScaledThirdJet
BalabanCMP102Eq80CutoffRadialResidual
BalabanCMP102Eq80CutoffCenteredResidual
BalabanCMP102Eq80SourcePi4DomainEnumeration
BalabanCMP102Eq80SourcePi4IndexedCutoffResidual
```

By contrast, the modules named
`BalabanCMP102Eq80PhysicalFineHeadTail*` control individual walk/summand
layers and remain reusable inputs for decay and summability.  They do not by
themselves construct the complete domain activity consumed by
`potential_bound`, and no such module is to be counted as a terminal
discharge until an exact reassembly theorem identifies its sum with that
activity.  This distinction prevents the old fine-head/tail candidate from
surviving silently after the target object changed.

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

The first support layer for that proof is now closed.
`BalabanCMP98ContourFirstVariationSupport.lean` proves that the oriented
Wilson generator is zero when the underlying positive-bond coordinate is
zero, propagates this fact through the literal recursive contour variation,
and identifies it with the ambient Fréchet derivative.  In particular, a
single-bond probe has exactly zero first variation on every contour which
avoids that physical bond.  The result is exact support, not exponential
smallness and not a supplied kernel certificate.  It remains to prove from
the definitions of the three `cmp99SourceUbarGamma` paths and the coarse
bond path that, for `c ≠ c'`, all four contours appearing in the row `c'`
avoid the pivot bond `b₀(c)`.  That source geometry will then feed this
support theorem to produce the off-diagonal vanishing of `K_U`.

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

## Native Lemma-1 residual ledger (2026-07-31)

The Lemma-1 domain mismatch is now handled without an artificial bijection or
a quotient by coincident coarse supports.  Every literal connected native
`2`-block domain remains a distinct finite index; its support alone is mapped
to the CMP116 `M`-block lattice.  This avoids summing coarsification fibres in
the residual activity and preserves the native tree metric from equation
(2.30).

`BalabanCMP109Lemma1Eq136SourceCertificate` pins the restricted residual to
the literal equation-(2.12) energy difference, with positive `E0` and a
small-field predicate containing zero.  The analytic (1.36) estimate remains
an explicit source hypothesis.  `BalabanCMP109Lemma1CoarsenedResidualFamily`
then constructs the finite native enumeration and exact energy-difference
sum.  Finally `BalabanCMP109Lemma1NativeRootedResidual` derives the centered
equation-(2.20) rooted residual bound from:

```text
native connectivity + degree 8 + exact M^4 root preimage
+ equation (2.30) + two explicit 64q < 1 animal windows.
```

Visual reinspection of the primary CMP116 page 9 corrects the small-field
dictionary: (1.34) says `|B| < epsilon1 * gk^{-1} on Y` and states that the
localized function depends on `B` restricted to the interior of `Y`.  The
certificate therefore projects the fluctuation field to the bilateral bonds
whose two endpoint sites lie in `Y.blocks`; it no longer imposes the ambient
sup norm.  The later centered region `Z0` is a separate object and may contain
the selected large-field bonds `P`.  It must not be reused as the small-field
cutoff carrier: doing so makes the signed cutoff identically zero for
nonempty `P`, as recorded by the formal no-go theorem.

Thus the combinatorial `rooted_residual` field is discharged for this sector;
the analytic Lemma-1 bound, final `domain_subset`, `volume_budget`, and the
complete terminal constructor remain open.  The detailed field-by-field audit
is `docs/source-db/reports/CMP109-LEMMA1-NATIVE-RESIDUAL-AUDIT.md`.
