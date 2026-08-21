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

## Primary-source check of CMP102 equation (80)

The acquired CMP102 primary PDF (`1104114383.pdf`, SHA-256
`838056B5C578F81D058DEB3D394C66D934690E3B94C6CF2956534EC6D211B541`)
was rendered at printed page 290 / PDF page 14.  The source prints

```text
V(A') = -<H D_3(A'),J> - <A',Delta_pi H D(A')>
        + (1/2)<H D(A'),Delta_pi H D(A')>
        + V_0(A' - H D(A')).
```

This agrees term for term with `cmp102Eq80GlobalPotential`: both negative
signs, the coefficient `1/2`, the order of each pairing, and the shifted
argument of `V₀` are identical.  CMP102's `H` is rectangular (coarse field to
fine field), and the corresponding literal physical specialization is
`cmp102Eq80SourcePi4RectangularWeakenedPotential`.  The square
`cmp102Eq80SourcePi4RealMixedPotential` uses the same four-term algebra but
specializes `H` to a fine-field covariance; it is not by itself the source
dictionary for the rectangular minimizer.  The render used for this check has
SHA-256
`BA6FD739924166FE5A98DC3F931C9998EF596913922B33C6E216EF0446B62A7A` in the
private source cache.

This source check validates the literal equation-(80) formula.  It does **not**
identify the source symbols `H`, `Delta_pi`, `J`, `D`, `D_3`, `V_0`, and `A'`
with their physical Lean realizations; that source-to-Lean dictionary remains
open and must not be absorbed into this formula check.

### Equation (78): the missing `D`/`D₃` dictionary

Immediately above (80), CMP102 prints

```text
<H D(A'),J> = <H C^(2)(A'),J> + <H D_3(A'),J>.                 (78)
```

The accompanying source construction separates the second-order term
`C^(2)` from the order-at-least-three remainder `D_3`.  In the corresponding
source region and coordinate convention this is the intended decomposition
`D = C^(2) + D_3`, equivalently `D_3 = D - C^(2)`.  The current Lean
equation-(80) core instead accepts `D` and `D₃` as independent maps and links
them only through separate zero-normalization assumptions.  Therefore the
named open obligation is

```text
cmp102.eq78.D3-equals-D-minus-C2:
  transport the source-region C^(2)/D/D_3 decomposition to the literal
  physical Lean maps used by cmp102Eq80GlobalPotential.
```

Equation (78) displays the identity after applying `H` and pairing with `J`.
It must not be promoted to an unrestricted global function equality until
the preceding source definition, region, and coordinate frame have also been
transported.

### CMP volume 102 disambiguation

Communications in Mathematical Physics volume 102 contains two consecutive
Balaban papers whose equation numbering starts again at `(1)`:

- `cmp102_uv3d`: *Ultraviolet Stability of Three-Dimensional Lattice Pure
  Gauge Field Theories*, pp. 255-275, equation range `(1)`-`(71)`;
- `cmp102_variational`: *The Variational Problem and Background Fields in
  Renormalization Group Method for Lattice Gauge Theories*, pp. 277-309,
  including equations `(78)`, `(80)`, and `(142)` used here.

A tracked-citation sweep found one bare multi-equation string containing
numbers at most 71, `CMP102 (22), (44)-(46), (142)`, in the live
Gaussian-root/Hessian catalog.  The same string includes `(142)` and its
recorded page locators 281/285/299, so it is unambiguously the variational
paper.  The other literal bare citation is `CMP102 (80)`, also outside the
UV3D paper's equation range.  No tracked citation was found that presently
attributes an equation `(1)`-`(71)` to the wrong paper.  Future citations in
that range must name `cmp102_uv3d` or `cmp102_variational`, not merely the
volume.

### CMP98 acquisition status

The CMP98 source is **not yet a clean registered primary-PDF acquisition in
this workspace**.  The canonical-looking file
`runtime/sources/primary/cmp98-averaging.pdf` is a 1157-byte Incapsula HTML
response, not a PDF.  A separate extracted text and two page renders are
present under `tmp/pdfs/cmp98`, so the paper has partial local source material,
but Proposition 2 has not yet been visually certified from a registered clean
primary artifact.  Its use as the source anchor for existence of `U_k` in the
regularity class therefore remains `located`/dictionary-open rather than
source-verified.

## `CMP116Eq226PhysicalContourTermSource` field audit

The source record is the first object that must be constructed physically.
Its current status against the CMP102 lane is:

| Record component | CMP102 producer status |
|---|---|
| `contour` | **non-circular constructor exists**: `CMP116Eq214PhysicalContourDensity.ofSourcePi4RestrictedPhysicalContour` starts from a private neutral dependent shell and overwrites the potential, bond field, and full restricted complex Gaussian from physical producers; no inhabited contour density is an input |
| `source` | physical Gamma/operator ingredients and their complex-contour installation exist; source faithfulness still depends on the literal indexed potential/remainder ledger supplied to the constructor |
| `domainMetric`, `domainCard`, `domainSupport` | the combined direct/native dictionary and its nonemptiness/subset laws are installed by the compiler-verified source-specific `PreEq136` assembler |
| Cauchy-radius identities | generic CMP116 formulas exist and the target identities are explicit fields of `PreEq136`; their source-specific installation is still pending |
| positivity/smallness scalars | many scalar lemmas exist; no complete source record |
| `outer_bound`, `inner_bound`, `source_bound` | generated in the centered-conditioned physical contour lane from the covariance/contour producers, subject to the named contraction and scalar windows; they are not consequences of equation (80) alone |
| contour `potential` summand | **combined partial ledger constructed**: the direct Eq-80 fixed quadratic core and cubic Taylor residual are literal, and direct (1.36) is derived from the physical third-jet/walk producers; the native Lemma-1 residual is separately indexed and carries its named restricted source certificate; installation in a complete pre-source and the remaining printed species are open |
| `interaction_bound` | **open at installation level**: the direct (1.36) and combined Eq-219/rooted ledgers now have producers, while the native analytic (1.36) remains the explicit CMP109 certificate; the final centered AE potential bound and scalar interaction budget have not yet been assembled into `PreEq136` |
| `domain_nonempty`, `domain_subset` | discharged for the combined direct/native dictionary, with the centered region enlarged rather than silently dropping boundary domains |
| `rooted_residual` | direct and native producers are combined under one explicit root bound and installed by the verified source-specific assembler |
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

The proof-carrying localized-region repair, generated conditioned root and
strict covariance-lower certificate, and the prescribed-`qBound` reduction
were then validated at source checkpoint
`fe9a2cd3e9344a5a63a0087f3e5009a56bf9644f` by durable GitHub Actions run
`30962182007`.  The dictionary and combined-source focal builds completed
8527 and 8978 jobs; the `qBound` wall completed 8202 jobs.  All 29 audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
The downloaded deterministic evidence archive has SHA-256
`b158aa22fd02e38813502f0e8876f422f73b13bdb0d4cc31805937bc6238456d`.

| Obligation group | Source status |
|---|---|
| non-circular contour density | producer compiled: `ofSourcePi4RestrictedPhysicalContour`; the literal direct/native potential adapter still supplies its inputs |
| combined `total` / `residual` ledger | exact direct/native definitions and sum identities compiled |
| `domainMetric`, `domainCard`, `domainSupport` | canonical appended dictionary compiled |
| `domain_nonempty`, `domain_subset`, `domainMetric_nonneg` | producers compiled for the enlarged centered region |
| `rooted_residual`, `rootBound_nonneg` | direct/native combined producers compiled and installed by the source-specific assembler |
| `volume_budget` | exact combined physical volume-rate producer compiled; scalar target remains visible |
| equation (1.43) | combined physical producer and source-specific terminal-field adapter compiled; neither accepts a free Hessian estimate |
| equation (1.36) | direct sector derived from CMP102 jets and walks; native sector is the named positive, nonempty-small-field CMP109 certificate; the combined finalizer is compiled but still requires a `PreEq136` inhabitant |
| literal `kernelSupport`, `metric_budget` | source definitions and proofs compiled in the clean focal queue |
| `smooth`, `hessian_zero_off_support` | source proofs compiled from the projected direct core and zero native core |
| covariance range (`sourceRange_bound`, `finiteRange`) | literal interacting-precision producer compiled and installed |
| covariance/parametrix contractions and contour bounds | remain explicit physical producer inputs; no source-specific pre-record yet assembles all of them |
| conditioned Gaussian root and covariance lower certificate | generated and installed from the literal interacting precision and the proof-carrying localized carrier; neither is an independent source datum |
| scalar windows (`shell`, contour/Neumann, root, outer, interaction, volume) | individually named; the joint target registry is inhabited, but physical attainment of `root_small`, `outer_small`, and the remaining operator bounds is still open |

Under the 41-obligation grouping above, the current auditable numerator is

```text
20 / 41
```

The twenty independently produced entries are: the non-circular contour
density; literal `total` and `residual`; literal `domainMetric`, `domainCard`,
and `domainSupport`; `domain_nonempty`, `domain_subset`, and
`domainMetric_nonneg`; `rooted_residual` and `rootBound_nonneg`;
`volume_budget`; equation `(1.43)`; literal `kernelSupport`; `metric_budget`;
`smooth`; `hessian_zero_off_support`; and the literal covariance-range
package (`sourceRange_bound`, `finiteRange`); together with the generated
conditioned Gaussian root and strict covariance-lower certificate.  Equation `(1.36)` is
deliberately outside this denominator.  The canonical `E0`, `threshold`, and
`alpha` equalities are not added to the numerator while their only terminal
use still passes through an already inhabited `PreEq136` record.

The table below retains the newly closed rows 12a and 13 so that their route
remains auditable, and retains auxiliary bridge 12b even though it is outside
the raw denominator.  Excluding those closed/auxiliary rows, the live
complement is `21 / 41`.  These are **obligation groups**, not raw Lean
fields: a group may contain the sign
conditions and structural certificates which have to be inhabited together.
"Partial producer" means that the physical expression or a propagation
theorem already exists, but at least one source-facing hypothesis or joint
smallness inequality is still an input.  It does not increase the 20/41
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
| 12a | conditioned Gaussian root (`conditionedRoot`) | **exact** square-root/support certificate | **producer installed** from the literal compressed covariance at `fe9a2cd3`; counted in `20/41` | tree |
| 12b | **localized covariance compression bridge** | **exact** compression/root identification plus quantitative upper/lower bounds | **complete source-facing bridge**: the analytic bounds from `460c05e5` and the literal proof-carrying localized carrier were jointly installed and compiler-verified at `fe9a2cd3`.  This bridge is outside the raw denominator. | tree; CMP99 [14] can sharpen the lower constant but is not required by the terminal type |
| 13 | strict conditioned covariance lower certificate (`conditionedCovariance_nondegenerate`) | **some positive** lower bound plus carrier nonemptiness; no optimal eigenvalue bound | **producer installed** from the interacting precision and literal nonempty carrier at `fe9a2cd3`; counted in `20/41` | tree, downstream of groups 2 and 12b |
| 14 | sigma Cauchy-radius normalization (`deltaRadius_eq`) | **exact** equality against the installed contour | open equality against the installed base contour | tree |
| 15 | cardinality normalization (`normalizedGap`) | **exact** equality in the chosen convention | open equality in the source convention | tree |
| 16 | tau Cauchy-radius normalization (`yRadius_eq`) | **exact** equality against the combined metric | open equality against the combined domain metric | tree |
| 17 | outer-series window (`qBound_nonneg`, `qBound_lt_one`) | **threshold** `0 <= qBound < 1` | open joint scalar window | tree + corpus: CMP116 |
| 18 | source-amplitude hierarchy (`E0Direct_nonneg`, `epsilon1_pos`, `epsilon1_le_one`, `C1_pos`, `alpha4_pos`, `C3_nonneg`, `C3_le`, `amplitude_nonneg`) | signs and ordered **source bounds**; faithfulness fixes the printed `C3` formula | partial; formulas are fixed, joint source inequalities are open | tree + corpus: CMP116 |
| 19 | block/exponent hierarchy (`one_le_M`, `eight_le_q`, `one_lt_kappa1`, `source_budget`) | **source threshold** hierarchy | partial source-facing scalar regime | tree + corpus: CMP116 |
| 20 | direct third-jet envelope (`hD`, `hD₃`, `hV₀`, `hC`, `hRjet`, `hsourceJet`, `sourceJetBound_nonneg`) | **source bounds** on the literal physical maps | partial CMP102 producer; the printed component estimates remain hypotheses | tree + absent: CMP102/[15] source text genuinely bites here |
| 21 | walk factorization and Eq.-(1.43) budget (`cardRatio_nonneg`, `metricRatio_nonneg`, `summationRatio_nonneg`, `walk_split`, both decay rates, `cardDecay`, `metricDecay`, `walk_small`, `eq143_budget`) | **source bounds plus thresholds** on the literal walk ratios | partial producer; these inputs already feed the verified Eq.-(1.43) conclusion | tree + corpus: CMP116; source provenance still audited field by field |
| 22 | residual/rooted animal windows (`residual_rate_nonneg`, `rooted_rate_nonneg`, `animal_small`, `rooted_animal_small`) | **threshold** windows | the simultaneous target witness is compiler-verified at `9e4161dc`; physical residual-rate production and the deferred Mayer input remain open | tree + corpus: CMP116 + absent: Cammarota [26] for the deferred Mayer input |
| 23 | canonical interaction/root stability (`alpha_pos`, `gamma_nonneg`, `root_small`) | **threshold** on the physically linked root | open scalar wall at the least admissible `alpha`; the physical root/covariance bridge is now installed, so the remaining task is attainment of the literal gap inequality | tree, downstream of groups 2, 12b, and 13 |
| 24 | outer Gaussian stability (`outer_small`) | **threshold** coupled to the same `alpha` and root | open scalar wall; the physical root has been eliminated from the sufficient bound, but the literal `qBound` gap budget and nonnegativity inputs remain to be attained | tree, downstream of groups 2, 12b, and 13 |

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
the selected marked carrier `P` may itself be empty.  Requiring `P.Nonempty`
would therefore exclude valid direct-branch terms.  The verified repair
instead indexes the physical source by the literal combined localized region
together with a proof that its transported coordinate carrier is nonempty.
That witness may come from either branch and is consumed directly by the
strict covariance-lower producer; no independent nonemptiness hypothesis is
introduced into the terminal record.

There is a terminal interface obstruction one level above that local
producer.  The former
`CMP116Eq226CenteredConditionedPhysicalTermSourceFamily` quantified over every
raw `Z0`, not merely over members of `Z0Index`; hence it asked for a term
source at `Z0 = ∅`.  The literal localized coordinate carrier is empty there,
while the mandatory covariance-lower certificate contains a
`carrier_nonempty` witness.  The source-level no-go theorem is present under
compiler-verified audit: no centered-conditioned physical term source exists
at the empty raw region.

The faithful repair is compiler-verified at `fe9a2cd3`.  The new
`CMP116SourcePhysicalLocalizedRegion Dict` is the subtype of regions whose
literal localized-coordinate carrier is nonempty, and the centered physical
family together with its `ToRaw`/`ToKP`/`ToUV` consumers quantifies over that
proof-carrying index.  The existing generic resummation already accepts an
arbitrary index type, so Appendix F remains unchanged.  This does not
fabricate a covariance certificate or an off-index physical term.  Its
nonempty carrier now feeds the generated root and strict lower certificate;
those two terminal producers, not bridge 12b itself, move the live numerator
from `18/41` to `20/41`.

The subtype repair does **not** yet construct that index for every tuple of
combined source data.  In
`CMP116CenteredConditionedCombinedSourceData`, both `localizedRegion` and
`localizedRegion_eq` remain supplied fields.  The anchor alone cannot
discharge them at this generic level: the definition of
`cmp116Eq80Lemma1CombinedCenteredRegion` contains only the selected direct
domains, the native expansion supports, and `P`.  With `domains = empty`,
`E.terms = empty`, and `P = empty`, both the block-domain family and the bond
carrier reduce to empty, hence so does the localization core and its
localized-coordinate carrier.  Thus an anchor-only nonemptiness theorem is
false for the present interface.  The remaining producer obligation is to
show nonemptiness for the actual physical enumeration (or to prove explicitly
which tuples contribute); it may not be replaced by a free nonemptiness
hypothesis or by silently dropping the all-empty tuple.

Elaboration failures are triaged separately from project mathematics.  If the
first error occurs in a proof step whose statement and diagnostic mention no
project declaration, variants are tested first in a minimal file importing
only the smallest relevant Mathlib module.  This applies not only to instance
synthesis, but also to generic algebraic rewrites, matrix identities,
orientation of inequalities, and normalization of norms or inner products.
The full hRpoly target is retried only after that reproducer elaborates.  This
keeps a generic Mathlib experiment from consuming a fresh full-project Colab
bootstrap for every candidate proof.

Dependent-family elaboration follows a fixed repair order.  First, do not
transport a family through `Function.update`: split the distinguished index
from the `Fin.succAbove` branch and state the required equality explicitly in
each case.  Second, pin the carrier, fibre and source/target indices in every
physical specialization rather than asking inference to recover them through
the generated tower.  Third, when the first error is only a missing imported
`.olean`, materialize that exact frontier target before changing the proof.
These three repairs have closed the recurrent elaboration stalls in this lane;
raising heartbeats or adding a broad transport lemma is not the default next
step.

The accumulated scalar gates are now centralized in
`CMP116CenteredConditionedJointSmallnessRegime`.  Its fourteen threshold
fields are: patched defect, shell, contour series, the two Neumann bounds,
the literal gap `alpha < coercivityConstant`, the literal joint outer budget
`2 * R1Budget + sourceRate / (coercivityConstant - alpha) <= qBound`, the
interaction budget, `qBound < 1`, the grouped-walk contraction, the two animal
contractions, and the two physical CMP109 pivot conditions.  The source value
at `L = 4` is used literally, `delta = (1/10)(1 - 2/4) = 1/20`; the exact
logarithmic rates give explicit factor-two margins.  A single witness inhabits
the whole record.  Adding or changing a scalar gate therefore breaks that
witness until the joint regime is updated, instead of silently leaving an
older compatibility claim in the tree.  This witness proves simultaneous
compatibility of the targets; it does not prove that the literal physical
coercivity, `R1`, or `R3` producers attain them.

Thus `20/41 -> 41/41` is the route to the first source-specific
`TermSource` **conditional on the named Lemma-1 certificate**.  Proving the
analytic Lemma-1 instance of equation (1.36) is a separate step which removes
that condition; it is not one of these twenty-one remaining pre-(1.36)
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
| `cmp99SourceBlockAverageWeight M d` | normalized mass of one generated `Q'` row at one blocking scale | exactly `M^-d`; this is a row mass, not a count of the `M^d` fine sites in the owner block |
| `cmp99SourceFlatQprimeOffsetAmplitude d M z` | source-normalized Fourier amplitude of one complete `M^d` offset fibre | the single coefficient `M^-d` multiplies the full offset sum and equals exactly the printed product `cmp89Eq245EntireAverageAmplitude d M z`; it is not applied once per coordinate after the sum |
| `(cmp99SourceBlockAverageWeight M d)^depth` | normalized row mass of the depth-`depth` generated counting tower | exactly `(M^-d)^depth`; every induction step contributes one new normalized row mass |
| owner-block count times one-scale row mass | cancellation between counting and averaging units | `M^d * M^-d = 1`; never replace the normalized row mass by the raw owner-block cardinality or apply the normalization a second time |
| `L` in the source-separated regional route | RG block ratio of the generated tower | controls the precision range `L^(depth+1)` and the Poincare/coercivity package `CP(L)`; it is held fixed when the independent large-block parameter grows |
| `K` in the source-separated regional route | source's sufficiently-large regional parameter (printed as `M`, renamed in Lean) | controls the cell side `K * L^(depth+1)` and cutoff spacing `2*K*L^(depth+1)`; it does not enter `CP(L)`, but the later covariance dictionary must still retain CMP99 Theorem 3.15's separate `M * alpha_0` smallness condition |
| `cmp99Eq342RescaledBlockDist (L^(depth+1)) (K*Q)` | source localization-block distance for CMP99 (3.42)/(3.89) | measures separation in units of `L^(depth+1)` on the `2*(K*Q)` block carrier; this is the metric required by the printed exponential |
| `cmp99Eq342RescaledBlockDist (K*L^(depth+1)) Q` | separated regional-cell distance used by the currently sealed coordinate-kernel specializations | measures only in units of the full `K*L^(depth+1)` cell; it is a valid coarser metric but is not the source localization metric and cannot be substituted for it in (3.89) |
| old one-parameter regional specialization | diagonal comparison `K = L = M` | all existing identities remain exact, but this diagonal object does not realize the source freedom used to attain the contraction |

Consequently, an interface whose `domainCard` is `blocks.card` must never
multiply that value by another `M^-4`.  The printed prefactor `alpha4*M^-4`
is a different amplitude normalization and remains present.  The two
conventions are kept distinct in every equation-(1.43)/(2.19) budget.

The repository's `FinitePiLpTypedWeightedRowKernelBound` uses a
**source-fixed** convention: it fixes the input delta and sums over output
targets.  The displayed kernel identity (3.88) instead fixes the output
site `x` and sums over input sites.  The literal generated physical precision
is symmetric, but for vector-valued blocks symmetry alone does not identify
the two vector-by-vector sums.  Any source claim that needs the printed
fixed-output orientation must therefore provide an explicit adjoint/block
bridge (or prove that orientation directly); the source-fixed bound may still
be used for the repository's delta-propagation compositions without silently
renaming it as the printed row.

The fixed-output orientation is now produced directly for the literal
generated counting mass and for `Q'^*Q'`.  The complete physical precision
then retains, in its public amplitude, the literal sum of the
nearest-neighbour Laplacian budget and the scalar-mass multiple of the
normalized counting budget.  These theorems were compiler-verified at
checkpoint `db04d33a19be5f4e87d842f6cc9a3925e53f4388`; they are inputs to,
not a replacement for, the still-open exact three-term identity (3.88).

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

The second layer is now represented by the type
`CMP116CenteredConditionedJointSmallnessRegime`, whose fields contain all
fourteen threshold conditions currently exposed by the centered CMP116
consumer and the physical CMP109 pivot.  The parametric value
`cmp116CenteredConditionedJointSmallnessRegimeWitness d L Nc` inhabits that
registry for every `d`, `L`, and nonzero `Nc`; adding another window to the
registry therefore makes the witness fail to elaborate until compatibility
is re-established.  This witness was compiler-verified in one fresh Colab
CPU/high-RAM clone at source checkpoint `9e4161dc4ea74e7846fc80bedc81f8bb5d2ae45a`.
The focal target completed with 8,755 jobs in 1793.774 seconds, and the audit
exited zero in 10.380 seconds with all eight declarations depending exactly
on `[propext, Classical.choice, Quot.sound]`.  The evidence archive has
SHA-256 `5b9c061c80bdcd1d8e098d554bdea17292f669cfad21c8743464c2c84acf96da`.

This is a compatibility theorem for explicit target envelopes, not a proof
that the literal physical operators attain them.  It closes the stale
eight-window bookkeeping problem but does not increase the live `18/41`
producer numerator or construct a `TermSource` inhabitant.

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

## Lemma-1 printed-proof route (2026-08-02)

Visual inspection of CMP116 pages 5--8 turns the analytic Lemma-1 certificate
from an opaque source hypothesis into a nine-brick route.  This is a source
map, not a Lean discharge: the live producer numerator remains `18/41`, and
no `TermSource` inhabitant is created.

| brick | printed content | repository status |
|---|---|---|
| L1 | `s`-dependent propagators `H(s)`, `G(s)`, `H0(s)` and the walk estimate entering (1.11) | **generic printed deduction compiler-verified**: the propagator is constructed internally as the weakened walk `tsum`, the `m <= 16` / `m > 16` split gives `B0 * exp(16*kappa1)`, and the cited CMP99 per-walk estimate remains an explicit source input; physical `H/G/H0` identifications remain separate |
| L2 | uniform fixed point `D(H(s),A')`, (1.13)--(1.14) | **compiler-verified parameter-family generalization** of `BalabanCMP109ConstraintCorrectionFixedPoint`; the physical `s`-polydisc specialization remains downstream of L1 |
| L3 | fixed point `A0`, (1.15)--(1.16) | new; consumes the printed CMP102 Proposition-4 type estimate |
| L4 | assembly and norm of `H_k(s,B')`, (1.17)--(1.18) | composition of L1--L3 |
| L5 | `B' = g_k C B - h D(g_k C B)` and its small-field bound, (1.19)--(1.20) | literal field already present |
| L6 | FTC in `s` and connected-component regrouping, (1.9)--(1.10) | Eq.-(80) weakening/FTC substrate exists; physical re-instantiation remains |
| L7 | Cauchy extraction (1.23) and termwise estimate (1.24) | new but source-local; the cited CMP109 input is in the corpus |
| L8 | summation (1.26)--(1.28) to (1.29) | animal/cardinality and normalized-metric substrate exists |
| L9 | scale comparison and final delta allocation to (1.36) | new scale-geometry lemma plus the visually verified windows `delta1 * M >= kappa1`, `(kappa1 - 1) / 4 >= (1 - delta) * kappa`, and `kappa1 / 16 >= (1 - 2 * delta) * kappa` |

The exact visual source record is
`cmp116.lemma1.window.1.11-1.29`.  It corrects an important OCR error: the
case split before (1.13) is `m > 2^4`, not `m > 24`.  Consequently the
repository factor `exp(-decay/24)` must not be cited as a literal recovery of
that split; it belongs to a different animal-count normalization.  The same
reading has an internal numerical check: in the complementary case
`m <= 2^4 = 16`, positivity of `kappa1` gives
`exp(m*kappa1) <= exp(16*kappa1)`, exactly the factor printed in (1.18),
(1.21), and (1.39).  This check does not identify the unrelated `/24`.
The same visual pass fixes the constants in (1.13)--(1.16), the Cauchy radius (1.22),
the structure of (1.24), and the final `exp(-kappa1 d_k(Y)/16)` rate in
(1.29).

A subsequent visual inspection of printed page 9 records the exact L9
allocation.  Equation (1.31) is
`d_j(X) >= (L^j * eta)^(-1) * d_k(X0)`.  The passage from (1.30) to
(1.32) assumes `(kappa1 - 1) / 4 >= (1 - delta) * kappa` with
`0 < delta < 1`; the final common decay in (1.36) assumes
`kappa1 / 16 >= (1 - 2 * delta) * kappa`.  Together with the earlier
walk absorption `kappa1 <= delta1 * M`, these are the three printed scalar
windows.  The former provisional readings with factors `1/2` and `7/8`
are rejected.  This source recovery does not discharge L9 in Lean.

L2 is now implemented by
`CMP109ConstraintCorrectionParameterFamilyData`.  Its `ballData` varies with
the admissible parameter `s`, while `rho`, both radii, and
`contraction_lt_one` are single common scalars outside that quantifier.  The
fixed point is selected internally from the existing literal CMP109 map; no
family of solutions is accepted as input, and `admissible_nonempty` excludes
the empty-polydisc witness.  One fresh Colab CPU/high-RAM clone at source
checkpoint `de7c13a59083c2b2000bb722203f9afd22aaae5d` completed the focal
build with 8,511 jobs and its four-declaration audit with the exact standard
axiom trio.  This closes the generic uniform Banach brick, not its physical
specialization and not any `PreEq136` field; the live numerator remains
`18/41` and no `TermSource` inhabitant is produced.

L1 is now implemented by
`CMP116Lemma1WeakenedPropagatorCertificate`.  It accepts the source walk
terms, active carriers, tree lengths, and the CMP99 `(3.108)`-shaped
per-walk majorant, but it does not accept a preselected family of
propagators.  Instead it constructs the literal complex weakened `tsum`,
proves its fully coupled value, coordinatewise derivative, and the uniform
equation-(1.11) bound on the whole `|s(Delta)| <= exp(kappa1)` polydisc.  The
printed threshold is the visually verified `2^4 = 16`; the repository's
unrelated `/24` animal normalization is not used.  One fresh Colab
CPU/high-RAM clone at source checkpoint
`6f5a3c9730ce49c77c028d618600c7dfa611a5ee` completed the focal build with
2,756 jobs and the seven-declaration audit with exactly the standard axiom
trio.  This closes the generic L1 deduction only.  The three physical
specializations remain separate, and the literal `H0(s)` producer is still
absent.  The live numerator remains `18/41` and no `TermSource` inhabitant is
produced.

The subsequent physical-specialization audit separates two genuinely
different tasks.  For the covariance propagator
`cmp116SourcePi4FullComplexWeakenedCovarianceMatrix`, every finite-walk term
is already definitionally
`cmp116ComplexWeakeningMonomial active sigma` times an `s`-independent
physical operator.  Its length layer is exactly the finite sum of those
terms.  Specializing generic L1 to this `G(s)` therefore needs only the
dependent reindexing
`Sigma length, CMP99SourcePi4FineWalkIndex ... length` and a justified
`tsum_sigma` exchange.

The repository's algebraic minimizer family has a stricter obstruction.  The theorem
`cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_literalFineWalkSeries_of_source`
expands it into a head fine-walk term times an ordered word of coarse-defect
fine-walk terms.  Every factor depends on `sigma`; overlapping active
carriers can therefore contribute repeated powers of one coordinate.  The
existing `cmp99SourcePi4FineHeadTailActive` records only the union needed for
locality and does not turn those repeated powers into the squarefree `Finset`
monomial used by generic L1.  This historical audit originally proposed a
multiplicity index.  The primary-source correction recorded below supersedes
that proposal: the printed `H(s)` is a different, directly weakened
generalized-walk series and must be constructed from its union carrier.
`H0(s)` still has no literal producer.  This audit changes no counter.

The physical covariance specialization is now compiler-verified.  For every
matrix entry it instantiates the generic L1 certificate with the dependent
walk index
`Sigma length, CMP99SourcePi4FineWalkIndex M Q R length`, performs the
summable reindexing, and identifies the internally constructed propagator
exactly with `cmp116SourcePi4FullComplexWeakenedCovarianceMatrix`, the literal
physical `G(s)`.  A single `treeLength`, `baseWeight`, and scalar budget is
shared by every row/column pair before `s` is quantified, so this does not
hide an entry-dependent or post-selected polydisc budget.  The result is an
exact entrywise `G(s)` bridge; scalarization alone does not provide a
volume-uniform operator-norm estimate.  The direct squarefree generalized-walk
producer for the printed `H(s)` and a literal `H0(s)` producer remain separate
open inputs.  One
fresh Colab Pro+ CPU/high-RAM clone at source checkpoint
`d21ba0ecde1fcffaf4e1c2060eb35823d12384f6` completed the focal build with
8,491 jobs and the three-declaration audit with exactly the standard axiom
trio.  This physical bridge changes neither the live `18/41` producer count
nor the number of `TermSource` inhabitants.

The multiplicity obstruction in the literal minimizer `H(s)` is now resolved
at the level of one complete physical word.  The module
`BalabanCMP116WeakeningMultiplicity.lean` represents overlapping carriers by
finitely supported natural exponents and proves the exact powerset expansion
of `prod_i (m_i(s)-1)`.  The physical module
`BalabanCMP99ComplexFineHeadTailMultiplicityExpansion.lean` then extracts
these scalars from the literal ordered matrix word without commuting any
matrix factors.  Each complete head/tail word is exactly a finite signed sum
of multiplicity monomials multiplying one unchanged sigma-independent
physical matrix word.  No disjointness of walk carriers is assumed.

One fresh Colab Pro+ CPU/high-RAM clone at source checkpoint
`17f416433ca6ea95b7cf38d414d3bccf878cec13` completed the focal build with
8,491 jobs in 1,466.565 seconds.  The generic and physical audits exited zero
and printed ten declarations, all with exactly
`[propext, Classical.choice, Quot.sound]`.  The complete gate recorded
`FINAL_STATUS=PASS`; its downloaded evidence archive has SHA-256
`132e8766327fa5e1a05aa5d1b7e190e7e0ebedc91330901d75c2c88e3c9b4bdd`.

This closes the exact finite-word algebra only.  This historical next-step
description is superseded by the primary-source correction below: total
multiplicity degree controls the auxiliary algebraic family, not the printed
squarefree `H(s)`.  The latter must use the cardinality of the distinct
visited carrier in generic L1.  The module supplies neither that direct
physical walk producer nor a literal `H0(s)` producer.  Therefore the live
producer count remains `18/41` and no `TermSource` inhabitant is produced.

The finite identity is now lifted through the complete literal physical
`H(s)` series.  The theorem
`cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_nestedMultiplicitySeries_of_source`
retains the source nesting
`Neumann length -> coarse word -> tail choice -> head length -> head walk`
and replaces only each terminal word by its exact finite powerset sum of
multiplicity monomials.  In particular it neither interchanges two infinite
sums nor commutes physical matrix factors.  One fresh Colab Pro+ CPU/high-RAM
clone at source checkpoint
`5ae463a2e48bc91d582672ba64dbbac51f4c1f6f` completed the focal build with
8,492 jobs and the one-declaration audit with exactly
`[propext, Classical.choice, Quot.sound]`; the independently rehashed evidence
archive has SHA-256
`ef52812ec6826038096e29f3fb9d976d966e66420a6bc176c46965e7ede92df7`.

This closes the exact whole-nested-series algebra for physical `H(s)`, not its
analytic L1 estimate.  Flattening the nested index, proving absolute
summability of the expanded terms and controlling total multiplicity degree
remain separate.  A literal `H0(s)` producer is still absent.  The live
producer count therefore remains `18/41` and no `TermSource` inhabitant is
produced.

The total-degree radial majorant is now compiler-verified independently of
that remaining source estimate.  The module
`BalabanCMP116WeakeningMultiplicityMajorant.lean` defines the total degree of
a finitely supported weakening multiplicity, proves that degrees add, and
identifies the degree of a finite family with the sum of the individual
carrier cardinalities even when carriers overlap.  A uniform coordinate cap
then bounds each multiplicity monomial, and each multiplicity-weighted term,
by the corresponding radial power.  This is finite algebra: it neither
absorbs the powerset cardinality nor identifies its degree with the printed
CMP116 integer `m`.

One fresh Colab Pro+ CPU/high-RAM clone at source checkpoint
`ca21ccc18e7918800e169dcd25a1db9235bfed58` completed the focal target with
`Build completed successfully (2757 jobs).` in 33.063 seconds.  The focused
audit exited zero in 3.612 seconds and all five declarations depend exactly
on `[propext, Classical.choice, Quot.sound]`.  The complete gate recorded
`FINAL_STATUS=PASS` after 134.710 seconds; the visible transcript was saved
and independently rehashed on Windows as
`e372fa7da5a08073965ec1a863fc42c54bda308ebf81df9dc7ab36b9669f044d`.
The runtime was disconnected and deleted immediately afterward.  This brick
changes neither the live `18/41` producer count nor the number of
`TermSource` inhabitants.

The exact finite powerset cost is now compiler-verified as a second, separate
brick.  For one omitted-subset term, the radial exponent is bounded by the
head carrier cardinality plus the sum of all tail carrier cardinalities.  The
sum of the norms of the complete finite expansion is therefore bounded by
exactly `2 ^ indices.card` copies of that common radial majorant.  No sign
cancellation is used and no infinite sum is rearranged.

This theorem deliberately does **not** identify `indices.card` with the
integer `m` in the printed CMP116 split `m > 2^4`.  It also does not absorb
`2 ^ indices.card` into a contour ratio or a source walk weight.  Those are
the remaining source-to-series dictionary and summability obligations.

One fresh Colab Pro+ CPU/high-RAM clone at source checkpoint
`1e7e3bb4` completed the focal target with
`Build completed successfully (2758 jobs).` in 30.177 seconds.  The focused
audit exited zero in 3.976 seconds and all four declarations depend exactly
on `[propext, Classical.choice, Quot.sound]`.  The complete gate recorded
`FINAL_STATUS=PASS` after 192.292 seconds; the visible transcript was saved
and independently rehashed on Windows as
`89e225ae8432711a2d503c8f401ff488645d178b69ceb8a24770fbf8a1f0e59b`.
The runtime was disconnected and deleted immediately afterward.  The live
producer count remains `18/41` and there is still no `TermSource` inhabitant.

The norm-producing part of generic L1 is now generalized to total weakening
multiplicities.  `BalabanCMP116Lemma1MultiplicityPropagatorBound.lean`
constructs the multiplicity-weighted complex `tsum` internally and proves
the same `B0 * exp(16*kappa1)` bound from one summable base-weight budget and
one long-walk estimate written in the total multiplicity degree.  A physical
instantiation must therefore pay the finite powerset cost inside that
base-weight summability and prove the degree/tree-length comparison; neither
is hidden in the certificate.

This is the norm conclusion needed before the L2 fixed-point family.  A
multiplicity monomial is not affine in one coordinate, so the square-free
coordinate-derivative proof is not reused: coordinatewise holomorphy and the
later Cauchy extraction remain separate bricks.  The theorem also makes no
identification between total degree and the printed CMP116 integer `m`.

One fresh Colab Pro+ CPU/high-RAM clone at source checkpoint
`49d92ea4c93c1875960db957271df08d27ec6f58` completed the focal target with
`Build completed successfully (2760 jobs).` in 23.567 seconds.  The focused
audit exited zero in 5.450 seconds and all nine declarations depend exactly
on `[propext, Classical.choice, Quot.sound]`.  The complete gate recorded
`FINAL_STATUS=PASS` after 125.203 seconds; the visible transcript was saved
and independently rehashed on Windows as
`15dd1a44036d7a84e43b42d9ffd8853f2e6e0df4c1887ea30e22dc10231a7d7a`.
The runtime was disconnected and deleted immediately afterward.  This is a
new proof compiler for the physical L1 bridge, not a new terminal producer:
the live count remains `18/41` and no `TermSource` inhabitant is produced.

Primary-source correction after that brick: printed page 3 defines the
weakening monomial of each propagator random walk using the set of all
**distinct** `sigma_0` cubes intersecting its localization domain.  Hence the
printed monomial is squarefree and the integer `m` counts distinct cubes.
The repository object
`C(s) Q* (Q C(s) Q*)^-1`, when expanded algebraically, has repeated powers
from overlapping factors.  It agrees with the physical rectangular
minimizer at `s = 1`, but no theorem identifies it with the printed
squarefree `H(s)` for general `s`.

Consequently the multiplicity modules above remain valid algebra and valid
majorants for that auxiliary algebraically weakened object, but they do not
constitute the physical specialization of CMP116 equation (1.11).  A
squarefree series cannot be obtained by merely regrouping repeated powers:
`s(Delta)^2` is not `s(Delta)`.  The source-faithful route must instead start
from the union monomial on each generalized walk.  The existing chain
`BalabanCMP116VisitedWeakeningFactorization` ->
`BalabanCMP116RestrictedVisitedTransferPowers` already implements this exact
visited-carrier algebra.  The next physical brick is therefore a direct
identification of its head readout with the printed `H(s)`, followed by the
tree-length estimate for the distinct visited carrier.  No live producer
counter moves at this correction.

The acceptance gate for that next brick is now fixed before any further
flattening.  It must construct, entrywise, a series of the form

`sum_omega (prod_{Delta in active(omega)} s(Delta)) * term(omega)`,

where `active(omega)` is literally the `Finset` union of the localization
carriers of the CMP99 generalized walk.  The family `s |-> H(s)` may not be
an input.  The admissible source inputs are instead the sigma-independent
walk term, the per-walk CMP99 estimate, the long-walk geometry in
`active(omega).card`, the summable base-weight budget, and the exact
full-coupling reconstruction `sum_omega term(omega) = H`.  Generic L1 then
constructs the weakened family internally.  If the visited-state transfer
presentation is used computationally, its rectangular head/readout must be
proved equal to this same squarefree `tsum`; it does not define a second
notion of weakening.

In particular, neither total letter degree nor the multiplicity expansion of
`C(s) Q* (Q C(s) Q*)^-1` may enter the physical dictionary.  Repeated
occurrences of one cube remain visible only in that auxiliary algebraic
family.  This gate leaves one genuinely source-cited input open: the concrete
CMP99 rectangular generalized-walk reconstruction of the physical minimizer.
The citation is not equation (3.107) alone: (3.107) is the series for the
square propagator `G`; the rectangular minimizer is represented by (3.126),
and Theorem 3.12 transports the random-walk conclusions to `H`.  The named
input must therefore encode that composition.  Moreover the paragraph after
(3.133) says that the literal variational-problem operator inserts the
coordinate factor `(U eta)⁻¹` (or transforms the input data equivalently), so
the equation-(3.126) auxiliary cannot silently be identified with the final
physical minimizer.  It is narrower than accepting an arbitrary weakened
`H(s)` family and makes the missing source content explicit.

Two tempting shortcuts are excluded.  First, evaluating the current
fine-head/tail word expansion at `s = 1` and weakening those terms again does
not produce the missing source walk expansion.  Its tail factors are relative
defects which vanish at full coupling, while the surviving term still carries
the unexpanded full-coupling coarse covariance.  Second, retaining the
omitted-subset inclusion--exclusion does reconstruct the minimizer at full
coupling, but it is precisely the auxiliary algebraic family retracted above;
replacing each multiplicity by its support does not identify it with the
printed family.

The physical walk index must therefore be fixed only after the CMP99
rectangular random-walk reconstruction is made explicit.  CMP99 printed page
427 does describe a later `H1` expansion as tree-like, but that is not the
linear weakening object used here.  The relevant source chain is: generalized
linear walks for `G` in (3.107), the rectangular formula
`H = G Q* (Q G Q*)^-1` in (3.126), and Theorem 3.12 for the resulting `H`
random-walk conclusions.  Importing the later `H1` tree geometry into this
dictionary would be another object mismatch.  The existing visited-state
algebra therefore has the correct linear shape.  What remains is to extend its
square transfer product by the source's rectangular head/readout and to
identify the resulting unweakened series with the physical minimizer.

`BalabanCMP116Lemma1RectangularVisitedWalk` supplies a compiler-verified
**fixed-carrier auxiliary specialization**: one `R0(X0)` head, square
continuation factors on a common state space, the exact union carrier, the
visited-product identity, an internally assembled squarefree propagator, and
its entrywise Eq. (1.11)-shaped bound.  The source checkpoint
`0ee9133a1b0c3d0eeaebcd3d9964e3ae06476ca9` passed a fresh Colab Pro+ focal and
five-declaration audit on 2026-08-03.  That compiler result remains valid for
the generic theorem, but it does **not** close the physical algebraic shape.

CMP99 printed page 413 states that the intermediate `R'_alpha(X)` factors
generally act between different scales, that not every label sequence is
admissible, and that this typing is omitted from the displayed formula only
because it does not affect the bounds.  The physical bridge must therefore use
the existing `DependentArrowWalk`/heterogeneous Section-C carrier machinery,
or prove an additional common-ambient reduction preserving every ordered
product.  No such reduction exists today.  Moreover the reconstructed
displayed alphabet is explicitly incomplete because CMP99 says "etc.".  The
remaining named input is consequently the **dependent**, complete-alphabet
identity `sum_walk walkTerm = physicalH`, justified by the (3.107) `G` series,
the rectangular formula (3.126), and Theorem 3.12, not the fixed-carrier
certificate's reconstruction field.  No free weakened family is accepted,
and no live producer counter moves at this correction.

There is one further endpoint gate that must remain visible.  The generic
dependent certificate fixes both its source and target, whereas the current
displayed Section-C generator returns
`Sigma target, DependentArrowWalk ... source target`.  A physical
specialization must therefore do one of two literal things: prove that the
complete source alphabet forces the common terminal carrier required by the
physical operator, or supply the printed rectangular endpoint readout and
prove that summing its readouts over the sigma target gives the same
`physicalH`.  Silently forgetting the sigma target is not an admissible
dictionary step.  This is an endpoint/type obligation inside the exact
(3.126)/Theorem-3.12 reconstruction, not a second analytic hypothesis and not
a terminal producer.

That endpoint gate is now compiler-verified.  In a fresh Colab clone at
`fe5bfdd288eacee5239bc458abb225bf1ce55209`, the target-total module completed
`8458` jobs and all four oracle declarations reported exactly
`[propext, Classical.choice, Quot.sound]`.  The theorem fixes the required
sigma-indexed sum and its weakening/analytic consequences; it still receives
the single total physical reconstruction as the named CMP99 source input and
therefore does not discharge that input.

The primary CMP99 paper itself is not an acquisition blocker here: equation
(3.107) for `G` is visually confirmed on printed page 416 / PDF page 28,
(3.126) for `H` is visible on printed page 420, and Theorem 3.12 is visible on
printed page 423; the source-db records CMP99 as `visual_confirmed`.  The
remaining debt is the source-to-Lean reconstruction just described--in
particular the exhaustive typed atom/parser, the rectangular composition, its
coordinate conversion, and the endpoint readout hidden behind the printed
"etc."--not the absence of the paper.

The printed word "etc." does not force Lean to postulate an arbitrary list of
missing `alpha` labels.  The tree already has a more primitive exhaustive
route: `BalabanCMP99SourceEq395WalkExpansion` expands the literal three-species
correction in (3.95) into every ordered **top-level correction word**, and
`cmp99Eq395PhysicalCorrectedCovariance_eq_canonical` identifies its convergent
Neumann sum with the canonical covariance.  Those three species are themselves
composite summands: they still contain the internal `G`/`G'` factors that the
printed Section-C argument expands before it assigns grouping roles.  It would
therefore be semantically wrong merely to label each top-level (3.95) atom as
one of the printed anchor/attachment roles.

The missing source parser has an additional exact stage.  For every (3.95)
species it must expand all internal `G` and `G'` occurrences into a dependent
factor word, expose the small `K(h') G h'` anchors and the at-most-three
nonsmall `h' G' h'` or `h C h` factors, and prove that evaluating that internal
word recovers the original composite summand.  Only then may it apply the
printed closest-anchor rules--attach `h' G' h'` to the closest small factor on
the right and `h C h` to the closest one on the left--prove the attachment
bound, adjoin the patched-parametrix head, and transport the grouped word
through the rectangular readout above.  Thus the open boundary is not a mere
role assignment on the existing raw word: it is the exact per-species internal
factor expansion followed by the source grouping parser.  The examples hidden
behind "etc." must be generated from that expansion, not guessed.

There is an exact squarefree bridge for the already specialized Pi4
covariance, `cmp116Lemma1PhysicalCovariancePropagator_eq`.  It identifies the
entrywise L1 series with the literal physical `G(s)`, but it does not identify
that Pi4 object with every regional `C_D` or `G'` occurrence inside the three
(3.95) species.  It is therefore reusable substrate for the internal expansion,
not yet a producer of it; a regional/source-carrier dictionary is still
required before any of those factors can be replaced by that series.

### Regional-Green gates exposed before physical specialization

The regional Theorem-3.7 compiler has two distinct acceptance conditions.
They must not be merged.  Mere support inclusion
`supp h_Pi ⊆ Omega_Pi` is sufficient for the exact compressed-inverse
algebra.  The physical commutator estimate additionally needs the quantified
collar

`finiteRange < dist(supp h_Pi, complement Omega_Pi)`.

The latter is a named geometric predicate, not an implicit property of the
partition.  It is consumed only by the future producer that proves locality
and smallness of the regional defect.

Likewise, `norm R' < 1` is a new regional zero-cochain contraction target.
It is not the existing one-cochain `patchedDefect_small` field.  The joint
smallness registry therefore carries it as a separate fifteenth target; its
rational witness proves simultaneous compatibility only, not physical
attainment.  Neither addition changes the live `18/41` numerator or produces
a `TermSource` inhabitant.

Both gates are now compiler-verified at source checkpoint
`efc23a559b71c29a87c50b562506d984d277de7f` in one fresh Colab Pro+
CPU/high-RAM clone.  The regional module completed 8,507 jobs and its eleven
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.
The joint smallness module, including the independent regional-defect target,
completed 8,755 jobs and all eight audited declarations use the same exact
axiom set.  This verifies the regional inverse algebra, the explicit
finite-range collar contract, and simultaneous scalar compatibility.  It does
not prove the physical locality estimate or that the physical regional defect
attains the fifteenth target; the live counters therefore remain `18/41` and
`TermSource = 0`.

### Current superseding checkpoint (2026-08-05)

The later source checkpoint `fe9a2cd3e9344a5a63a0087f3e5009a56bf9644f`
installs the literal proof-carrying localized carrier, generates the
conditioned covariance/root and strict lower certificate from the interacting
precision, and passes 29 focused axiom audits in durable run `30962182007`.
Consequently rows 12a and 13 are now discharged and the live producer count
is exactly `20/41`.  Row 12b remains infrastructure outside the denominator;
the regional target `norm R' < 1`, `root_small`, and `outer_small` remain
unattained physical/scalar walls.  No `TermSource` inhabitant is produced.

Source checkpoint `fbb2d47d5fbc0ccc4900c15b55cc210d9a8e0440` then removes the
physical conditioned-root norm from the remaining groups 23--24 inputs.  The
combined assembler now derives `root_small` from the literal coercivity gap
`alpha < coercivityConstant`, derives nonnegativity of the literal restricted
`R3` source rate from the already named Neumann windows, and derives
`outer_small` from the visible joint gap budget
`2 * R1Budget + sourceRate / (coercivityConstant - alpha) <= qBound`.
Durable run `30965959088` verifies that reduction and all 32 focused axiom
blocks.  These are still scalar attainment obligations rather than new
terminal producers, so the live count remains exactly `20/41`, `TermSource`
remains zero, and physical attainment of the regional target `norm R' < 1`
also remains open.

The same two literal gaps replace the obsolete `rootNorm`/`outerBudget`
targets in the joint compatibility registry at source checkpoint
`c4beb733a1df50ded144c83c390de35d4cfa17ef`.  Durable run `30969049527`
verifies one rational witness for the complete updated registry and all eight
focused axiom blocks.  This prevents the compatibility result from silently
lagging behind the consumer interface, but it does not show physical
attainment and therefore leaves `20/41` and `TermSource = 0` unchanged.

The regional prerequisites below CMP99 (3.88) were then replayed from source
checkpoint `837040284f5ce1d358d42eb8f6c01689829db29b` in durable GitHub
Actions run `30971247380`.  The verified set comprises the CMP95 periodic
active-cell overlap and linear cutoff slope, the auxiliary generated fine
partition/slope and its arithmetic scale no-go, the normalized weighted-row
commutator estimate, the regional Green Neumann algebra, and the exact
additive split of the regional source-precision commutator.  All sixteen
build/audit stages exited zero and all 36 audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

These modules are **prerequisites/infrastructure for CMP99 (3.88), not a
terminal field**.  In particular, they do not prove the displayed physical
three-term identity, physical cutoff-slope attainment, `norm R' < 1`, groups
23--24, or a `TermSource` inhabitant.  The exact source-side construction
still has to expose the link-derivative term, cutoff-Laplacian term, and
normalized `Q'^* Q'` term before estimating their sum.  The live counters
therefore remain exactly `20/41` and `TermSource = 0`.

### Validation plane and first two species of CMP99 (3.88) (2026-08-05)

For this nonterminal internal brick, the owner-authorized GitHub Actions
plane is a reproducible remote alternative to Colab: it checks out an exact
raw source SHA, verifies the fixed Lean/Mathlib pins, emits durable logs and
hashes, and runs the focal and axiom audit stop-on-first-error.  Project build
caches are diagnostic only.  A cache-backed run may guide elaboration, but it
may not move a counter, retire a `PRE-VALIDATION` mark, or seal a brick.  The
seal must cite a cold checkout without restoration of `.lake/build`.
Terminal delivery still requires two independent fresh replicas under the
terminal policy; this intermediate authorization does not amend that gate.

Under that rule, source checkpoint
`767f54dd847b2459f05b2e2a9ea5ac320b8ccd35` passed cold GitHub Actions run
`30984221871`: the focal completed 8,474 jobs, the four-declaration audit
exited zero, and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.  The module derives the exact
link-derivative and scalar cutoff-Laplacian species from the literal periodic
covariant stencil.  The normalized `Q'^* Q'` term and the complete
three-species identity remain open.  This is infrastructure below physical
attainment of window 15, not a terminal producer, so the live counters remain
exactly `20/41` and `TermSource = 0`.

### Normalized third species of CMP99 (3.88) (2026-08-05)

Exact source checkpoint
`1cf90bee75d7927362c94ef338efc46f32153097` passed cold GitHub Actions run
`30986285981` without restoration or saving of a project build cache.  The
focal completed 8,466 jobs, its five-declaration audit exited zero, and every
declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

The new brick expands the scalar commutator at fixed output, preserves exact
addition and scalar multiplication, exposes the normalized `Q'^* Q'` kernel
sum with its mass coefficient still visible, and identifies the generic
source precision definitionally with the literal generated physical tower.
It does **not** yet combine that third species with the active-region
transport of the two differential species, prove the complete physical
(3.88), or attain window 15.  It is infrastructure rather than a terminal
producer, so the live counters remain exactly `20/41` and
`TermSource = 0`.

### Complete generated physical cutoff identity CMP99 (3.88) (2026-08-05)

Exact source checkpoint
`39905a39f58a7e039ebaf17420393a57871e3dac` passed cold GitHub Actions run
`30990024776` without restoration or saving of a project build cache.  The
focal completed 8,509 jobs, its seven-declaration audit exited zero, and every
declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

The brick now combines all three literal species of (3.88): the covariant
link derivative, the scalar cutoff-Laplacian correction, and the normalized
`Q'^* Q'` fixed-output kernel sum.  Extension and restriction remain visible
until the ambient product rule is transported to the active carrier.  No
finite-range collar, overlap estimate, or contraction premise is borrowed by
the exact identity.

This does **not** yet bound the resulting regional correction, prove
`norm R' < 1`, discharge groups 23--24, or inhabit a `TermSource`.  It is the
complete algebraic identity below window 15, not physical attainment of that
window.  The live counters remain exactly `20/41` and `TermSource = 0`.

### Fixed-output quantitative commutator bridge (2026-08-05)

Exact source checkpoint
`4e23216a121fc64451528ce050443ee460ce589a` passed cold GitHub Actions run
`30992627475` without restoration or saving of a project build cache.  The
focal completed 8,174 jobs, its two-declaration audit exited zero, and both
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The bridge estimates `[h,K]` directly in the fixed-output orientation printed
in CMP99 (3.88).  A pre-existing fixed-output weighted budget pays exactly
`slope * range`; no self-adjoint orientation transport and no range-ball
cardinality are introduced.  The same fixed-output sum then yields the
pointwise exponential kernel bound term by term.

This is still generic infrastructure.  It does not choose the physical
large-block cutoff, identify the common ambient/regional operator, estimate
the Green composition, attain `norm R' < 1`, discharge groups 23--24, or
inhabit a `TermSource`.  The live counters remain exactly `20/41` and
`TermSource = 0`.

### Generated physical precision weighted specialization (2026-08-05)

Exact source checkpoint
`6bef7974e800d80534e171a285a7ea5b90d324e4` passed cold GitHub Actions run
`30994320564` (workflow checkpoint
`23652ae655b663dbb1ba5f924ba747b53aae1b4b`) without restoration or saving
of a project `.lake/build` cache.  The focal completed 8,493 jobs, its
five-declaration audit exited zero, and all five declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The specialization keeps the covariant-Laplacian and normalized
`Q'^* Q'` fixed-output budgets as two separately named quantities and only
adds them in the literal generated physical precision endpoint.  It then
uses the sealed generic bridge to obtain both the fixed-output weighted
commutator estimate and its pointwise exponential kernel consequence.  The
carrier, Lie-coordinate fibre, and target/source indices are pinned in the
public signatures; no elaboration timeout is hidden by a heartbeat increase.

The cutoff remains an arbitrary Lipschitz scalar function.  This brick does
not yet install the source large-block profile, prove the ambient-to-regional
operator dictionary, compose with a regional Green operator, attain
`norm R' < 1`, discharge groups 23--24, or inhabit a `TermSource`.  It is
infrastructure below window 15, so the live counters remain exactly `20/41`
and `TermSource = 0`.

### Source large-block cutoff specialization (2026-08-05)

Exact source checkpoint
`de57d8790caaab5d5177b59a76f9057901da8c43` passed cold GitHub Actions run
`30997349504` (workflow checkpoint
`5c2457849e4e7d916090c772291e090a5ca31c67`) without restoration or saving
of a project `.lake/build` cache.  The focal completed 8,527 jobs, and its
seven-declaration audit printed exactly
`[propext, Classical.choice, Quot.sound]` for all seven declarations.

The brick transports the one `CMP95SourceSmoothPartitionProfile` through the
exact carrier equality, proves its literal generated-site Lipschitz estimate,
and specializes both the fixed-output weighted and pointwise exponential
commutator bounds.  The covariant-Laplacian and normalized `Q'^* Q'` budgets
remain separately named and are added only in the final cutoff budget.  The
source-scale cancellation is literal:
`slope * M^(depth + 1) = 4 * derivBound / M`.

This does not identify the active operator with a supported compression of a
common ambient precision, compose with a regional Dirichlet Green operator,
or prove the physical defect budget is less than one.  It is step 4 below
window 15, not attainment of that window or a terminal field.  The live
counters remain exactly `20/41` and `TermSource = 0`.

### Source-faithful signed cutoff slope (SEALED; regional reinstantiation open)

Checkpoint `a8a84c302ed116a49b41acc12b85f78aa905c2ea` replaces the
analytic slope input of the retired square-root periodization without changing
the already sealed generic commutator/Green algebra.  It proves the
one-dimensional signed-periodization bound from the union of the two endpoint
active windows, treats `Q = 1` by the explicit constant branch, exposes the
inverse physical scale after rescaling, and tensors the estimate with the
literal constant

`16 * derivBound / M0`.

The `16` here is four coordinate directions times the one-dimensional slope
constant `4`; it is not the later active-cell overlap factor.  Cold GitHub
Actions run `31072468845` (workflow checkpoint `085d1170`) restored no project
`.lake/build` cache.  The focal ran from `2026-08-06T04:55:07Z` to
`05:18:08Z`; the ten-declaration audit exited zero at `05:18:19Z`, and every
declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic evidence archive has SHA-256
`1206c3853e70aaec368c0afb0da7c42a3ebd9f67c248556b3e843964f88b5765`.
The axiom JSON has SHA-256
`c383a81aefd3104eda42af2e0b0582bd89d9d32d194cd08fac9a6b30837b5f21`;
the stage ledger has SHA-256
`f35e52ee2be2efc8dfcc3f388a8dd6db72198b590c9d464f63edfb17c66c8c9d`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

The existing active-cell window and its cardinal bound `<= 16` are geometric
and cutoff-independent.  Only the implication from nonzero cutoff to window
membership mentions the functional cutoff; for the signed cutoff it must be
reinstantiated through the exact identity `signed^2 = squareWeight`.  The
regional signed partition, that membership transport, the quadratic second
difference, both physical species, complete CMP99 (3.89), `norm R' < 1`, rows
23--24, and a `TermSource` inhabitant remain open.  This seal is infrastructure
below window 15, not attainment of that window or a terminal producer.  The
live counters remain exactly `20/41` and `TermSource = 0`.

### Signed source-separated partition and overlap (SEALED; species open)

Checkpoint `d77c64b8c5702ec833c853fffb0afbcf277f93a5` instantiates the
source-faithful signed cutoff on the literal separated large-block carrier.
The exact square partition is inherited from the signed square identity.  The
physical slope remains explicit:

`(16 * derivBound / cutoffScale) * precisionRange = 8 * derivBound / K`.

Thus the inverse independent large-block parameter enters before every later
cell or layer sum, while the factor two relative to the retired square-root
realization is visible rather than absorbed into an unnamed constant.

The active-cell implication is re-proved for the new functional cutoff by
transporting `signed^2 = squareWeight`; it then lands in the unchanged
geometric active window.  The pre-existing cardinal theorem consequently
gives the same literal pointwise overlap `<= 16`, with no new overlap datum.

Cold GitHub Actions run `31074140752` (workflow checkpoint `0b539caf`) restored
no project `.lake/build` cache.  The focal ran from
`2026-08-06T05:28:54Z` to `05:47:39Z`; the nine-declaration audit exited zero
at `05:47:46Z`, and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

The deterministic evidence archive has SHA-256
`25521f8976f4848cb18c318f242110fb1a0939620aef52eab2e5b710fc5d6200`.
The axiom JSON has SHA-256
`82634747e94ccfa1234f9fea470cf2f3e0d2a27b1bf306f1b6c4c67daf0df7cf`;
the stage ledger has SHA-256
`f67a9f7845361d6f7de0dd69d2b8af0ab44c5a3d6528479e2e5ef990d62f6c68`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This closes the cutoff-specific overlap exception but not the quadratic
second difference, either signed physical commutator species, the ambient /
regional dictionary reinstantiation, complete CMP99 (3.89), `norm R' < 1`,
rows 23--24, or a `TermSource` inhabitant.  It is infrastructure below window
15 and moves neither live counter: `20/41`, `TermSource = 0`.

### Signed periodic quadratic second difference (SEALED; tensor Laplacian open)

Checkpoint `f844f2faa3f27908581fd735933731dba37894da` transports the
canonical source-profile second-derivative budget through the signed linear
periodization.  The three evaluation points are rewritten over the union of
their literal two-point active windows, so at most six translates contribute.
Termwise application of the sealed profile estimate yields the exact bound

`12 * secondDerivBound * norm(h)^2`.

The explicit `Q = 1` branch is constant.  Physical rescaling is then proved
before tensoring, with literal inverse-square gain

`(12 * secondDerivBound / M0^2) * norm(h)^2`.

No positivity of the profile and no differentiation of a square root enter.
Cold GitHub Actions run `31076000837` (workflow checkpoint `05245920`) restored
no project `.lake/build` cache.  The focal ran from
`2026-08-06T06:05:06Z` to `06:28:17Z`; the three-declaration audit exited zero
at `06:28:26Z`, and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

The deterministic evidence archive has SHA-256
`a6ded498542500fa14033b0ac530c2729e7b8b58a13f79abbf36d0c7a7fce44d`.
The axiom JSON has SHA-256
`219b75d193e74d4c78de0a965ee632924ac39f8206dbf06ef0e6aa81b7ca0e03`;
the stage ledger has SHA-256
`2715f5f0981ed8c9668395bf079b970c46acd2c9c5b2e74ef11f7f00c753b400`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This is the one-dimensional analytic input, not yet the tensor
cutoff-Laplacian coefficient or the second physical species.  Tensor transport
through a torus coordinate shift, the ambient/regional dictionary, complete
CMP99 (3.89), `norm R' < 1`, rows 23--24, and a `TermSource` inhabitant remain
open.  Window 15 is compatible but unattained; the live counters remain
exactly `20/41` and `TermSource = 0`.

### Signed periodic tensor second difference (SEALED; source-separated transport open)

Checkpoint `4973182cf45705621a00adab78bb7756a1eb81e9` transports the
one-dimensional signed quadratic estimate through the canonical torus seam,
factors the tensor cutoff along the one active coordinate, and sums the four
literal directions.  The directional estimate retains

`12 * secondDerivBound / M0^2`,

and the complete scalar tensor-cutoff Laplacian coefficient retains the
explicit constant

`48 * secondDerivBound / M0^2 = 4 * 12 * secondDerivBound / M0^2`.

The proof pins the modular arithmetic in `Nat`, uses exact periodicity at the
two seam cases, and bounds the inactive tensor product by one.  It introduces
no Green norm, no cell-overlap factor, and no regional-compression hypothesis.

Cold GitHub Actions run `31079471965` (workflow checkpoint `1a6d50b7`) used
`COLD_MODE=true` and restored no project `.lake/build` cache.  The focal ran
from `2026-08-06T07:05:32Z` to `07:30:26Z`; the four-declaration audit exited
zero at `07:30:33Z`, and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.  The deterministic evidence archive
has SHA-256
`713ba250a1079b1f4199faf1060b36a1ae3405603d45138a99dff41ce0659a76`;
the axiom JSON has SHA-256
`5ccf1a60331bd6914ea6790f188cc2ac68a391ca27e192e270f3290da4cb7b92`;
the stage ledger has SHA-256
`9caae24ba47a3f919a524a6afcc53a7289093ab9e14a0e4f8fe73feadf590729`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This is the canonical tensor analytic core only.  Transport to the literal
source-separated carrier, identification with
`cmp99CutoffLaplacianCorrection`, multiplication by the regional Dirichlet
Green, the overlap-16 sum, complete CMP99 (3.89), `norm R' < 1`, rows 23--24,
and a `TermSource` inhabitant remain open.  Window 15 is compatible but still
unattained; the live counters remain exactly `20/41` and `TermSource = 0`.

### Signed source-separated cutoff Laplacian (SEALED; Green/overlap composition open)

Checkpoint `e14ea5903c3ab45179155d9fe530d29c442a78d3` transports the
canonical tensor coefficient through the literal equality

`sourceSeparatedSide * (2 * Q) = cutoffScale * Q`

coordinate by coordinate.  The transport covers both `shift` and `shiftBack`
without asserting a stronger definitional equality between dependent torus
types.  It proves the literal cutoff-side estimate

`norm coefficient <= 48 * secondDerivBound / cutoffScale^2`,

identifies that coefficient exactly with
`cmp99CutoffLaplacianCorrection ... 1`, and exposes the depth-scale
cancellation

`(48 * secondDerivBound / cutoffScale^2) * generatedRange^2
  = 12 * secondDerivBound / K^2`.

The Laplacian and normalized-mass species remain separately budgeted; this
brick does not absorb the factor into a shared precision constant.  Cold
GitHub Actions run `31082213055` (workflow checkpoint `063bd346`) used
`COLD_MODE=true` and restored no project `.lake/build` cache.  The focal ran
from `2026-08-06T07:48:16Z` to `08:13:47Z`; the four-declaration audit exited
zero at `08:13:55Z`, and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.  The deterministic evidence archive
has SHA-256
`888f5ecd71c67ca9e2da20581e6905b33efb5f10d88dfe5b46460a95958ff2ef`;
the axiom JSON has SHA-256
`7092d6184f160ccc86e82d8b7ad8a85686028a8efc39e979377e1b3b61c9f740`;
the stage ledger has SHA-256
`143cf54c14eb4fa8a0ee73966a26bbada6c766b9762902c7795613b0789046d4`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This seals the cutoff-side second physical species only.  The regional
Dirichlet Green multiplication, the overlap-16 cell sum, the third species,
complete CMP99 (3.89), `norm R' < 1`, rows 23--24, and a `TermSource`
inhabitant remain open.  Window 15 is compatible but unattained; the live
counters remain exactly `20/41` and `TermSource = 0`.

### Declared finite route from CMP99 (3.88) to `20/41 -> 22/41`

The bricks below are the complete declared route.  A green prefix is not a
counter movement; only the last two physical scalar producers, consumed by
the already verified assembler, discharge rows 23--24.

| step | nominal brick | exact output | status |
|---:|---|---|---|
| 1 | complete generated physical cutoff identity | the three literal species of (3.88) on the active carrier | **sealed** at `39905a39`, run `30990024776` |
| 2 | fixed-output quantitative commutator bridge | `[h,K]` pays `slope * range` in the printed orientation and yields a pointwise exponential kernel bound | **sealed** at `4e23216a`, run `30992627475` |
| 3 | generated physical precision specialization | the literal generated `K` supplies its finite range and two separately named Laplacian / normalized-mass row budgets | **sealed** at `6bef7974`, run `30994320564`; no counter movement |
| 4 | source large-block cutoff specialization | instantiate `h` by the one `CMP95SourceSmoothPartitionProfile`, use the source carrier equality, and rewrite slope times range to the exact `4 * derivBound / M` gain | **sealed** at `de57d879`, run `30997349504`; no counter movement |
| 5 | ambient-to-regional precision dictionary | realize the full generated active carrier as the literal ambient `FinBox`, transport the generated precision/coercivity and source cutoff through one explicit equivalence, and identify the regional commutator with the reindexed active commutator | **sealed** at `8ac1a1c2`, cold run `31001590888`; no counter movement |
| 6 | uniform single-cell regional correction | compose the cell commutator with the regional Dirichlet Green and the contractive right cutoff, retaining one explicit cell amplitude | **sealed** at `ddda0475`, cold run `31021829343`; no counter movement |
| 7 | direct source defect estimate CMP99 (3.89) | prove the printed `O(K^-1)` bound for the physical regional defect with the `K^-1` gain present before layer summation and the overlap `16` independent of `K`; derive `norm R' < 1` for sufficiently large `K` | **open**; the former CT + Schur reduction was sealed at `ef157f84` and then closed as a physical route by the no-go at `8494a73f`; it remains diagnostic infrastructure only |
| 8 | two literal centered-conditioned gap producers | prove `alpha < coercivityConstant` and `2 * R1Budget + sourceRate / (coercivityConstant - alpha) <= qBound` from the physical rates produced by the regional construction | open; the assembler then derives `root_small` and `outer_small` and moves the live count to `22/41` |

The `coercivityConstant` in step 8 is not an opaque positive scalar.  Its
physical producer must instantiate it definitionally as
`CMP116InteractingPhysicalPrecisionSource.coercivityConstant`, namely
`min 1 a / CP - cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc epsilon`.
Here `CP` belongs to the literal `FlatGaugeHodgePoincare 4 M (2 * Q)` package,
so the dependence on the block ratio `M` and its Poincare cost remains visible
in both gap inequalities.  The reduction to `alpha`, `R1Budget`, `sourceRate`,
and `qBound` stays inside step 8; it is not an unnamed step 7.5 and must not
replace the physical coercivity producer by a free constant.

Thus window 15 is necessary but is not silently identified with rows 23--24.
The path has a declared last element.  Step 5 has frozen the last design
dictionary.  Step 6 remains reusable regional infrastructure; step 7 is now
the source-analytic estimate (3.89), not another generic CT + Schur majorant;
step 8 consumes the resulting physical rates.

The `coercivityConstant` dependence enters both the regional Green input and
step 8 literally.  The direct (3.89) producer must keep the Poincare cost
`CP(L)` separate from the independently large `K`; neither may be absorbed
into an unnamed constant.

Step 7 is itself a finite source-facing chain; it is not the former generic
Schur step with adjusted constants:

1. expose the four local Theorem-3.1 estimates in (3.42) for the literal
   regional `G'_Pi`: value, left covariant derivative, right adjoint
   derivative and covariant Laplacian, with the common `B0`, `delta0` and the
   printed scale vector;
2. derive the first-difference and **second-difference** bounds of the one
   physical CMP95 cutoff at the separated scale `K * L^(depth+1)`.  The
   first derivative controls the link species.  The cutoff-Laplacian species
   must instead use a second-derivative budget derived from the already
   recorded `ContDiff` regularity and compact support of the selected source
   profile, so its coefficient is quadratic in the inverse cutoff scale
   before it meets the `ell^2` Green-value estimate.  No free profile constant
   may be added;
3. rewrite the third species of (3.88) by the exact generated `Q'^*Q'`
   transported-block formula and cancel its literal normalized row mass
   against the count before any cell or layer sum;
4. combine the three displayed species on coordinate probes, with `K^-1`
   already present and no reciprocal coercivity or Poincare constant.  This
   composition must specialize all three species to rescaled spacing `1` and
   must instantiate the differential background `U` by the dependent
   cast/reindexing of the **same** fine `background` that constructs the
   generated `Q'` tower, using
   `cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier`.  A sum whose
   first two species use an independently supplied `U` is only an abstract
   three-operator bound.  Even the physical coordinate-probe sum is still
   strictly weaker than the printed localized-action estimate (3.89);
5. prove the source-facing localized-action estimate for an arbitrary
   `lambda` supported in one source block, in the supremum norm fixed by
   CMP99 (3.39)--(3.42).  The existing
   `FinitePiLpTypedExponentialKernelBound` quantifies only
   `singleFinitePiLp source v`; expanding a general `lambda` into such probes
   and summing pays the cardinality of the fine fibre because
   `cmp99Eq342RescaledBlockDist` is constant on that fibre.  Such a factor
   would destroy the printed uniform `K^-1` gain and is not an accepted
   bridge.  The Green package and the three-species estimate must instead be
   upgraded to the block-localized sup-norm action that the source states.
   The source block metric must also be the `L^(depth+1)` localization scale
   printed in (3.89), not the separated cutoff-cell scale
   `K * L^(depth+1)`;
6. only then use the already sealed overlap `16`, independent of `K`, in the
   same source norm to obtain the defect contraction for sufficiently large
   `K`, and connect that contraction to the Neumann reconstruction.

The overlap input in item 6 splits into a geometric part and one
cutoff-specific transport.  The finite windows
`cmp95PeriodicActiveCellWindow` and
`cmp95PeriodicTensorActiveCellWindow`, together with their cardinality bounds
`2` and `16`, mention only residue classes and support geometry; they are
independent of `Real.sqrt` and remain unchanged for the signed linear
periodization.  The existing membership theorem
`mem_cmp95RescaledPeriodicTensorActiveCellWindow_of_cutoff_ne_zero`, and hence
`cmp99SourceSeparatedLargeBlockActiveCells_subset`, is specialized to the old
square-root cutoff.  It is therefore not silently reused.

Before the signed cutoff becomes the physical separated partition, step 7.2
has an explicit overlap-transport substep: define its rescaled separated
active cells, use the exact signed-square identity to turn cutoff nonvanishing
into nonvanishing of the same tensor square weight, and reprove inclusion in
the existing geometric window.  The bound `16` is then reused literally,
with no second overlap constant and no `K` dependence.  Thus no sealed
geometric overlap theorem is orphaned, but the old functional membership
lemma is not claimed for a different cutoff object.

The source-facing sum needs one further, explicit owner-fibre transport.
Pointwise overlap at a fine site is not identified definitionally with
overlap for an arbitrary field supported in a complete localization block.
The intended window is centered at the midpoint of that owner block.  Every
site in the fibre is at normalized distance at most `1 / (4 * K)` from the
center; together with the source-profile support radius `2 / 3`, every active
translate lies within `11 / 12 < 1` of the center.  Hence the same two residue
classes per coordinate, and therefore the same tensor bound `2^4 = 16`,
cover the whole fibre.  This must be a theorem derived from
`blockSite_eq_iff_cube`, not a second overlap hypothesis.

Expanding a supported field into `singleFinitePiLp` probes is permitted only
inside the exact proof that a cell outside this owner window acts by zero:
the three physical species already have single-probe zero lemmas, and
linearity then gives exact annihilation.  The numerical estimate itself must
sum the already proved arbitrary-field bounds over the at-most-sixteen active
cells.  Applying probe estimates to the norm would reintroduce the forbidden
fine-fibre cardinality and is not an admissible proof of item 6.

A transitive dependency audit makes the replacement boundary broader than
that overlap lemma.  The generic commutator identities and regional-Green
estimates are cutoff-agnostic, but the sealed *source-separated physical
specializations* select `cmp99SourceSeparatedLargeBlockSquarePartition`
definitionally.  That partition's value is the old square-root cutoff.  In
particular, the sealed source-separated slope, the physical first-species
specialization, the ambient/regional commutator dictionary, and the old
cutoff-Laplacian coefficient remain true for that old object but are not
producers for the signed cutoff merely because they contain no textual
occurrence of `Real.sqrt`.

The signed route therefore has a finite replacement chain before step 7 can
be called physical: construct the rescaled signed separated square partition;
derive its first-difference and quadratic second-difference bounds; transport
the overlap `16` as above; and reinstantiate the already sealed generic
first-species and ambient/regional dictionaries with that partition.  The
generic algebra is reused, not reproved.  The old specializations remain
sealed algebra for the square-root object and are explicitly retired as
physical producers for the signed route.

The fixed-output predicate currently available in
`FinitePiLpTypedFixedOutputWeightedKernelBound` quantifies one common fibre
vector over all source coordinates.  It therefore does not control the
`Q'^*Q' (single source (lambda source))` sum occurring in (3.88).  Step 7.3
must use the literal normalized block formula above; adding an abstract
varying-vector row is not, by itself, a source proof of (3.89).

There is a second, independent quantifier gate after that varying-vector
issue.  `FinitePiLpTypedExponentialKernelBound` itself is an entrywise
coordinate-probe predicate: it tests only `singleFinitePiLp source v` in the
stored finite `L^2` field.  The primary statements (3.42) and (3.89) instead
quantify an arbitrary `lambda` supported in one block and use the supremum
norm defined in (3.39).  Therefore a literal sum of the three physical
coordinate kernels is valid algebra below (3.89), but is not yet the printed
localized-action estimate.  No contraction or window-15 attainment may be
derived from it until the block-localized sup-norm producer in step 7.5 is
installed.  A generic entrywise-to-operator summation over fine sites is not
accepted because its fibre-cardinality loss can cancel the physical
`K^-1` gain.

The current physical specialization also exposes a scale gate in the metric.
`CMP99Eq342RegionalGreenCertificate` stores its decay through
`cmp99Eq342RescaledBlockDist m q`, whose `blockSite` divisor is `m`.  The
three-species specialization infers
`m = cmp99SourceSeparatedLargeBlockSide L K depth = K * L^(depth+1)` and
`q = Q` from the ambient carrier.  By contrast, the primary display (3.89)
has decay `exp (-delta0 * (L^j eta)^-1 * |y-y'|)` between the localization
blocks `Delta(y)` and `Delta(y')`.  Passing
`ell = L^(depth+1)` to the certificate changes the four amplitude powers but
does not change its metric.  Thus the existing common-metric component
lemmas are valid bounds on the coarser separated-cell metric, but they are
not yet the source metric producer.

The faithful repair must expose the same ambient carrier at localization
scale `m = L^(depth+1)` with `q = K * Q` (or an explicitly equivalent
terminal-block owner metric), and prove the required carrier/reindexing
dictionary.  Associativity and commutativity of the side lengths are not a
definitional identification and may not be hidden in inference.  This metric
repair and the arbitrary-localized-source repair are both required before
the coordinate-kernel assembly can feed (3.89), the defect contraction, or
window 15.

**Elaboration battle note.**  Physical specializations of the generated
PiLp tower must pin the carrier, fibre, and source/target index types in their
public signatures (`ι`, `g`, and typed lambda binders).  Type inference is
reserved for the generic leaf lemmas.  Three deterministic `whnf` timeouts
have now been removed by this same rewrite; increasing heartbeats is not the
accepted repair for this class.

### Source-separated prerequisites for the direct CMP99 (3.89) route (SEALED)

Exact source checkpoint `b90c3c2efbfa100b38a87cc3591c799f7499fd78`
passed cold GitHub Actions run `31041990728` (workflow checkpoint
`ad9d4493cf10fcda390465f696c6a01a36a1b0ba`).  The run recorded
`COLD_MODE=true` and skipped restoration and saving of `.lake/build`.
All six focal/audit stages exited zero.  The three audits cover 36
declarations; every printed axiom set is a subset of
`[propext, Classical.choice, Quot.sound]`, with no outside name.

The independently downloaded evidence archive has SHA-256
`b0a46d83e48b30ec9f16b86738e16f82985b8df42c771e67a867cde54bad0eb8`.
Its axiom JSON has SHA-256
`c3811bd50de0c2d5257f64c88b47e52f1491f53b98ed42925dc03f1c93210ec1`
and its stage ledger has SHA-256
`5bc7640a7edbe21b7f3f5772c8c3e4bc14b8db37eb447ac97fed690004717177`;
all 17 entries of the internal `SHA256SUMS` manifest were independently
rehashed and matched.

This seal covers exactly the source-separated large-block partition, the
physical cutoff with gain `4 * derivBound / K`, and the generated ambient
dictionary, together with their audits.  The auxiliary two-scale CT + Schur
budget remains PRE-VALIDATION and is not part of the accepted physical route.
These are admissible prerequisites for step 7.1--7.4, not the direct (3.89)
estimate itself.  Hence window 15 remains unattained, the live producer count
remains exactly `20/41`, and `TermSource = 0`.

### Step 7.2 cutoff-Laplacian species (SEALED algebra; physical majorant retracted)

Exact source checkpoint `972e8d115517c6f1f9bea97ec348bd0e31e1368d`
passed cold GitHub Actions run `31047332477` (workflow checkpoint
`369870b6a978f247ba416a9ef84478bc7ec256ce`).  The run recorded
`COLD_MODE=true`, skipped restoration and saving of `.lake/build`, built the
8,517-job focal, and exited zero in both focal and audit stages.  All six
audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The seal proves the two incident first-difference bounds in each of four
directions, their scalar discrete-Laplacian sum, and its exact identification
with the literal cutoff-Laplacian species of (3.88) at rescaled unit spacing.
Those algebraic statements remain valid.  They do **not**, however, supply
the physical uniform majorant.  CMP99 (3.42) gives the Green value component
the scale `B0 * ell^2`, whereas the sealed triangle estimate cancels only one
power of `ell`:

`8 * cutoffLaplacianBudget * L^(depth+1) = 32 * derivBound / K`.

Consequently its composition with the value estimate is exactly

`32 * B0 * derivBound * L^(depth+1) / K`,

leaving a positive RG-scale factor.  The first-difference majorant is
therefore retracted as a producer for the depth-uniform (2.44)/(3.89) bound;
this does not retract the literal identity or the coefficient inequality.
The accepted repair derives a finite second-derivative budget from the
existing smooth compactly supported source profile and proves a quadratic
inverse-cutoff-scale second difference.  Because the current periodic cutoff
is represented as `sqrt (sum h_k^2)`, that repair must also expose the
source's smooth nonnegative cutoff choice (or an equivalent smooth periodic
realization); smoothness of the underlying `h` alone does not justify
differentiating the square root at zero.

The first half of that repair is now compiler-sealed.  Exact source checkpoint
`aaafae326ab952d990c0efb6a66553f0d2a61add` passed cold GitHub Actions run
`31067778196`: compact support plus the existing `ContDiff` field produces a
canonical finite nonnegative `secondDerivBound`, and the exact coarse
composition theorem records the leftover factor
`32 * B0 * derivBound * L^(depth+1) / K`.  This seal does not identify a
periodic cutoff with the smooth source profile.  The selected continuation is
a sign-preserving linear periodization of the literal profile: for periods
with at least two cells, disjoint support must prove that its square is the
already sealed periodic square weight; the one-cell volume is a separate
branch.  Only after that dictionary is proved may the quadratic profile bound
feed the tensor cutoff-Laplacian species.

The independently downloaded evidence archive has SHA-256
`6f3e21e5a7b1c8c14cf484a03d9ef67f7171bcf271d4539d251a0497f25e005b`.
Its axiom JSON has SHA-256
`27e81215558b9c4cd4c6b909a6c6646d9813c18ef27e70fd3dd4a650eace06a7`
and its stage ledger has SHA-256
`30d0e8ba6c761af639ba9fd183410db44e1541d436867dc0b65e3b06cd6f0932`;
all 13 entries of the internal `SHA256SUMS` manifest were independently
rehash-verified.

This is retained as cutoff-side algebra and as a diagnostic coarse bound, not
as the physical cutoff-Laplacian producer.  The second-difference repair, the
four regional Green estimates (2.43), their combination into (2.44)/CMP99
(3.89), the defect contraction, rows 23--24, and a terminal field remain
open.  Window 15 therefore remains compatible but unattained, the live
producer count remains exactly `20/41`, and `TermSource = 0`.

### Quadratic source-profile second difference (SEALED; periodization open)

Exact source checkpoint `b6469e61f3db08f17d44c45c1db056841be20974`
passed cold GitHub Actions run `31069570903` (workflow checkpoint
`b55a1e7f7739b7af0f79f329d519aea196c60225`).  The checkout recorded
`COLD_MODE=true` and restored no project `.lake/build` cache.  The focal and
audit both exited zero; all three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The seal derives, from the canonical source-profile second-derivative budget,
a global Lipschitz estimate for the first derivative, a first-order Taylor
remainder, and the centred quadratic estimate

`norm (h(x+u) - 2*h(x) + h(x-u)) <= 2*secondDerivBound*norm(u)^2`.

The factor `2` is intentionally non-sharp and remains visible.  This is a
profile-level theorem only.  It does not identify the current square-root
periodization with the source profile and therefore does not yet feed the
physical cutoff-Laplacian species.  The accepted next dictionary is a linear,
sign-preserving periodization of the literal profile: disjoint support must
identify its square with the sealed square weight when the period has at least
two cells, while the one-cell volume remains an explicit separate branch.

The independently downloaded evidence archive has SHA-256
`1d792a3b75f75f1a3c515a2c04537f27e94adf5f3ac369e5264d6ba685d8df7f`.
Its axiom JSON has SHA-256
`8c1e625514797a3759591e27aed5d0ee7bcf6edb72abf37e4b1d7d582acf4a1e`
and its stage ledger has SHA-256
`78dbc802700b0f81424544ca4607d69f1f0616c13adcfa742aaa27b098aaa8ab`;
all 13 entries of the internal `SHA256SUMS` manifest were independently
rehash-verified.

This seal does not prove the periodic dictionary, the physical second species,
complete CMP99 (3.89), `norm R' < 1`, rows 23--24, or a `TermSource`
inhabitant.  Window 15 remains compatible but unattained, the live producer
count remains exactly `20/41`, and `TermSource = 0`.

### Sign-preserving periodic profile dictionary (SEALED; physical reinstantiation open)

Exact source checkpoint `85654369b0bf37f2242ad31326393c1ec47d82aa`
passed cold GitHub Actions run `31070579539` (workflow checkpoint
`4539b24130bdcf1248e47b88f25bb92062b8e095`).  The run recorded
`COLD_MODE=true`, restored no project `.lake/build` cache, completed the
8,494-job focal, and exited zero in both focal and audit stages.  All nine
audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed object periodizes the literal real CMP95 profile linearly, so its
sign is retained.  For `Q >= 2`, the printed support interval proves that the
two possible translates in one residue class cannot both be nonzero; hence
the square of the signed sum is exactly the already sealed periodic square
weight.  The `Q = 1` torus is handled by an explicit constant cutoff `1`, not
by a hidden lower-bound hypothesis.  Tensoring gives the exact finite square
partition in four dimensions.

The independently downloaded evidence archive has SHA-256
`555ff32a693c008234c7b424bdc32d44005bed1c0af2d87eda0b99d1b66ee2f3`.
Its axiom JSON has SHA-256
`7d70f260953c1a49cb08ab2a1093204f3f8633d2920fe4e87af00f59cdbaebb6`
and its stage ledger has SHA-256
`aa8795b19c1305b2a9c9901a109746576f80af34fbdcd77f2217f7b3b2c8c1ba`;
all 13 entries of the internal `SHA256SUMS` manifest were independently
rehash-verified.

This seal closes the periodic profile dictionary only.  It does not make the
old square-root-based source-separated physical specializations valid for the
new function.  The rescaled signed partition, its first- and second-difference
bounds, overlap transport, and the physical first-species/ambient-dictionary
reinstantiations remain explicit next steps.  Therefore the physical second
species, complete CMP99 (3.89), window 15, rows 23--24, and a `TermSource`
inhabitant remain open; the live counters stay exactly `20/41` and zero.

### Step 7.1 regional-Green source interface (SEALED)

`BalabanCMP99Eq342RegionalGreenCertificate` records the one source-facing
analytic input used by the direct route.  Its operator is definitionally the
canonical regional Dirichlet Green of the literal ambient precision; no Green
family is a field.  One common strictly positive `B0`, `delta0`, and scale `ell` control
the four CMP99 (3.42) components with the printed scale vector
`[ell^2, ell, ell, 1]`: `G'`, `D G'`, `G' D*`, and `Delta G'`.  The CMP96
(2.43) projection exposes exactly the value and left-derivative components.
The carrier is required to be nonempty.  Thus neither zero amplitude nor an
empty regional space can inhabit the source contract vacuously.

The decay metric is definitionally the source block-scale distance
`finBoxDist (blockSite M (2*Q) x) (blockSite M (2*Q) y)`.  A cold
seal of the earlier raw-fine-distance version was cancelled before the focal
completed: the render of CMP99 (3.42) and the rescaling immediately preceding
CMP96 (2.43) show that the printed exponential is measured on the rescaled
block lattice.  Retaining raw `finBoxDist x y` would demand a strictly stronger
source theorem and would introduce an artificial exponential loss in the
normalized `Q'^*Q'` species.  The metric is not a caller-supplied parameter, so
the correction cannot be inhabited by choosing a degenerate distance.

Exact source checkpoint `f08109f46eb3e41e25716f9156ee314b1760f7e9`
passed cold GitHub Actions run `31053742585` with `COLD_MODE=true`; no project
`.lake/build` cache was restored or saved.  The focal completed 8,508 jobs,
the audit exited zero, and all twelve declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The downloaded evidence archive
has SHA-256
`924b257e900c5dc200ab7163c5324bc07aa0d1d73c7948bd97bb11e73b1d1dcf`;
its axiom JSON has SHA-256
`316fa78f2b0fe174ced7f9f960ec372d1f7917fb34369f72d50fbe942be3e73d`
and its stage ledger has SHA-256
`bdddb5e4cfc75881975d7238a1f13bfada7f353221658ff2ef677875d3f8aa76`.
Every entry of the internal manifest was independently rehashed and matched.

This interface deliberately does not derive (3.42) from the existing
`2 / coercivity` Combes--Thomas estimate.  Doing so would import the
Poincare/coercivity wall into the direct (3.89) constant and recreate the
route already closed by the depth-zero no-go.  `B0` and `delta0` therefore
remain the named Theorem-3.1 source input until their physical producer is
formalized.  This seal closes only prerequisite 7.1: it does not attain window
15, move `20/41`, or inhabit a `TermSource`.

### Step 7.4a first covariant-link species (SEALED interface; physical estimate open)

Exact source checkpoint `ed7d4007af46ac8858326578f89dc6726de76665`
passed cold GitHub Actions run `31056707497` (workflow checkpoint
`a1d33287a3b9fd3ab01d000534691f29576e87c5`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
completed the 8,519-job focal.  Both focal and audit exited zero.  The three
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The seal proves the source-facing orientation that the first species needs:
at rescaled unit spacing the reverse incident difference has exactly the norm
of the literal forward covariant derivative at the shifted base point, by the
adjoint isometry of the actual gauge background.  It then bounds the complete
link species by the eight incident covariant-derivative entries.  No abstract
row/column symmetry, operator norm, Combes--Thomas estimate, Schur sum,
Poincare constant, or cell cardinality enters this step.  Separately, the
physical cutoff slope times the printed `B0 * L^(depth+1)` derivative scale is
proved exactly equal to `4 * B0 * derivBound / K`, before every cell or layer
sum.

The independently downloaded evidence archive has SHA-256
`37c104fdee6846685286162c3accac55d9307b7f82522349497a7e4ea5262f92`.
Its axiom JSON has SHA-256
`885e2ae07f89b40de03888c6c8b50f18547035985b72211353df8b75f170b745`
and its stage ledger has SHA-256
`901559c3011970ae664f2b9462593fd50819a7ffb16884ba60a68b2d8d402396`.
Every entry of the internal `SHA256SUMS` manifest was independently rehashed
and matched.

This is only the algebraic/orientation interface for the first species.  The
next producer must consume the literal left-derivative estimate from the
sealed (3.42) certificate and transport its block metric at the four shifted
sites.  It does not yet prove the pointwise first-species (3.89) bound, combine
the three displayed species, attain `norm R' < 1`, discharge rows 23--24, or
inhabit a `TermSource`.  Window 15 remains unattained and the live counters
remain exactly `20/41` and `TermSource = 0`.

### Step 7.4b regional-Green incident-metric bound (SEALED; common metric open)

Exact source checkpoint `ec36dd107c2dbfd2db003c331dce23d4d787b683`
passed cold GitHub Actions run `31058984443` (workflow checkpoint
`659083efed10ac4c54752ccdcbfc0203217cdec9`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
completed the 8,520-job focal.  Focal and audit exited zero; the audited
declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

The theorem applies the sealed CMP99 (3.42) `D G'` estimate to the canonical
regional Green probe and all eight oriented bonds incident to the output
site.  Its right side retains the exact source block metric separately at the
central site and at each of the four backward-shifted sites.  Thus the
analytic producer is real and source-facing: it neither accepts a convenient
metric nor assumes the still-missing geometry that collapses neighboring
block distances to a common output distance.

The independently downloaded evidence archive has SHA-256
`911e03835e0e49105a751a04418a5d40f15d7fc3b25f6db866fe8c79d20ff754`.
Its axiom JSON has SHA-256
`6b800194b86f5d9cfd2983a2dacf187f61de7155f404d14abdd0ffb302de2761`
and its stage ledger has SHA-256
`63b97cc4fa280faecf3843489428a83c06a4e5529a0921485231b42a3cf338cd`.
Every entry of the internal `SHA256SUMS` manifest independently matched.

This seal still does not prove the common-metric first-species (3.89) bound:
the next named geometry must show that one fine backward step changes the
literal block owner by at most one coarse step and pay the corresponding
`exp(delta0)` factor.  Nor does it combine all three species, attain
`norm R' < 1`, discharge rows 23--24, or inhabit a `TermSource`.  Window 15
remains unattained and the live counters remain exactly `20/41` and
`TermSource = 0`.

### Step 7.4c one-step block-owner geometry (SEALED; exponential transport open)

Exact source checkpoint `79b8f33b2d73dc62e5d34bbf475c56f52a5331f5`
passed cold GitHub Actions run `31061565085` (workflow checkpoint
`5e538d6856d5861f66208178a9754731bae4e387`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
completed the 8,521-job focal.  Focal and audit exited zero; both declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The quotient/remainder proof is literal.  A backward fine step either remains
inside its current `blockSite` fibre or, precisely when it crosses a lower
block face (including the periodic wrap), maps to the one-step backward coarse
neighbor.  Consequently its coarse Chebyshev displacement is at most one.
The comparison is constructed from `blockSite`; it is not a metric premise.

The independently downloaded evidence archive has SHA-256
`b83e41e29fa2772e9b632dcc820a65285adda4c139579fe8d3844cc2cdfe3a18`.
Its axiom JSON has SHA-256
`684448d443268c791b8435142fb1f1bb359e8f9536602b1f7e3acfa9f107747d`
and its stage ledger has SHA-256
`6677b456595821773ca62ce9cc745232a5499046b16840deab02a5a7fdae5b34`.
Every entry of the internal `SHA256SUMS` manifest independently matched.

This closes the geometry needed to transport each backward incident metric,
but not the real exponential inequality that pays its `exp(delta0)` factor.
The common-metric first species, all-species (3.89), `norm R' < 1`, rows
23--24, and a `TermSource` inhabitant remain open.  Window 15 is unattained;
the live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4d common-metric exponential transport (SEALED; complete first species open)

Exact source checkpoint `47d02e63a865bb75bba6f14d2da1a12e6a675fe2`
passed cold GitHub Actions run `31063213456` (workflow checkpoint
`92e8f3e8688c437b89fd215c342eb1dae7bc7c66`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
completed the 8,522-job focal.  Focal and audit exited zero; both declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The first theorem turns the sealed one-step block displacement into the exact
real exponential comparison, paying one visible factor `exp(delta0)`.  The
second applies that comparison to every backward incident regional-Green term
and rewrites the first covariant-link species against the one central block
metric.  The four-direction `Fin 4` sum and the pre-sum `K^-1` gain remain
visible; no overlap, layer, Schur, Poincare, or operator-norm constant is
introduced or absorbed.

The independently downloaded evidence archive has SHA-256
`1d03fe2b762ba4e61cc2f9b3d2d17e476ea717e6bbb3877a7f3622a8c84028b9`.
Its axiom JSON has SHA-256
`e96a3d24f8e50e7b8a612228263b957d963997905b6b57ce9b5d7ec2e1ec4d3f`
and its stage ledger has SHA-256
`57dc380a606a0ed4c898099b53779f11896956119301936ef1513534132f6437`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This seals the common-metric transport for the first displayed species only.
It does not yet finish that species' source-normalized endpoint, combine the
three species of CMP99 (3.89), prove `norm R' < 1`, discharge rows 23--24, or
inhabit a `TermSource`.  Window 15 remains compatible but unattained, and the
live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4e physical first-species endpoint (SEALED; remaining two species open)

Exact source checkpoint `68fea228b9f1e7061f73df078b94f4cca6d08c9e`
passed cold GitHub Actions run `31065483711` (workflow checkpoint
`c37d1eb0386c6f0840a5e20aa1de6b44fa1adc3b`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
completed the 8,523-job focal.  Focal and audit exited zero; both declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The endpoint specializes the cutoff to the literal source-separated square
partition and evaluates the four directions.  Its scalar is exactly

`4 * ((4 * B0 * derivBound) / Klarge) * (1 + exp(delta0))`.

Thus the inverse-`Klarge` gain is present before every cell, overlap, or layer
sum.  The independent large-block parameter is named `Klarge`; the regional
precision remains the separate operator `A` with its literal CMP99 (3.42)
certificate.  No shared constant conflates the two contributions to the
precision.

The independently downloaded evidence archive has SHA-256
`6603cf0b45e475725ec060e3295f8e55aa8a408c16e38eff6b8b78e83540f11c`.
Its axiom JSON has SHA-256
`3ab3832f8f2aefaadac5e753d76e540c9bd87063c380f748422cd6550832d827`
and its stage ledger has SHA-256
`32b4b8ec95a1363ad2b786bd8aba010c4dfbe73a6ff0d7bb18b5323937af4419`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This completes only the covariant-link species.  The cutoff-Laplacian and
normalized `Q'^*Q'` species still require their corresponding regional-Green
bounds and common-metric endpoints; the three-species CMP99 (3.89) estimate,
`norm R' < 1`, rows 23--24, and a `TermSource` inhabitant remain open.  Window
15 is compatible but unattained, and the live counters remain exactly
`20/41` and `TermSource = 0`.

### Step 5 ambient dictionary (SEALED)

Checkpoint `8ac1a1c2508f65e51d4eb89f81bf650780691cf6` freezes the
ambient-to-regional dictionary without accepting a physical operator equality
as input.  Its declared chain is:

1. the full coarse region on `2 * (M * Q)` is `Finset.univ`;
2. every complete-block lift of that region is proved to remain `Finset.univ`;
3. an explicit finite equivalence identifies its generated active-site type
   with the factored ambient carrier
   `FinBox 4 (M^(depth+2) * (2*Q))`;
4. the one ambient precision is defined by isometric reindexing of the literal
   generated physical precision, and its generated coercivity constant is
   transported as a theorem;
5. pulling the active source cutoff through the same equivalence is proved
   equal to the literal regional `CMP95SourceSmoothPartitionProfile` cutoff;
6. consequently the regional square commutator is proved equal to the
   reindexed active commutator, and its existing exponential kernel bound is
   transported without a new constant.

The final equality is the consumer-facing dictionary.  It is not a postulated
identification of two independently chosen precisions.  The regional Green
composition, the overlap/Schur sum, and `norm R' < 1` remain steps 6--7.
Cold GitHub Actions run `31001590888` compiled the focal in 8,529 jobs and
then verified all eleven audited declarations with exactly
`[propext, Classical.choice, Quot.sound]`.  The checkout restored no project
`.lake/build` cache.  This seal moves neither `20/41` nor window 15.

### Step 6 uniform single-cell regional correction (SEALED)

Checkpoint `ddda0475533573d02f1197340df0d216467702da` constructs, for every
source large-block cell, the exact finite-range-thickened Dirichlet region
and the canonical inverse of the compression of the one generated ambient
precision.  It transports the ambient exponential kernel estimate to that
regional Green, composes the already sealed physical commutator on the left
and the contractive source cutoff on the right, and retains one explicit
cell-independent amplitude.  No separately chosen regional/global Green
identity and no new constant is accepted from the caller.

Cold GitHub Actions run `31021829343` (workflow checkpoint `83b0b310`) set
`COLD_MODE=true`, skipped both restoration and saving of `.lake/build`, and
compiled the focal in 8,552 jobs.  The 16-declaration audit exited zero and
every declaration uses exactly `[propext, Classical.choice, Quot.sound]`.
The deterministic evidence archive has SHA-256
`d41bd0f4e0a792cbb631dbcc70c3d630df24e6b493521b503beae1b1dc7addd5`.

This is **step 6 infrastructure, not a terminal field**.  The overlap factor
`16`, the Schur/operator-norm estimate, the physical defect budget
`norm R' < 1`, and both scalar producers of step 8 remain open.  Thus window
15 is still compatible but unattained, the live producer count remains
exactly `20/41`, and `TermSource = 0`.

### Step 7 overlap / Schur reduction (SEALED; scalar attainment open)

Checkpoint `ef157f8471ac9b9b7a9b5d12c0502b2aa3fa279d` sums the literal
single-cell regional corrections with the already derived source overlap
`16`, retains the two exponential shell factors, applies the fixed-output
Schur estimate, and defines one explicit generated physical regional defect
budget.  It proves
`norm R' <= cmp99SourceGeneratedPhysicalRegionalDefectBudget` and derives
`norm R' < 1` only from the literal scalar premise that this budget is less
than one.  It does not prove that premise.

Cold GitHub Actions run `31028008613` (workflow checkpoint `908329ce`) set
`COLD_MODE=true`, restored no project `.lake/build` cache, and compiled the
focal with `Build completed successfully (8557 jobs).`  The seven-declaration
audit exited zero and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.  The gate recorded
`FINAL_STATUS=PASS` against Mathlib
`07642720480157414db592fa85b626dafb71355b` and the official
Lean `v4.29.0-rc6` asset.

The deterministic evidence archive has SHA-256
`79dc5433b7198181cfb87590b0de308231fadfbd38dae93f034f3b3748d3399f`.
The axiom JSON has SHA-256
`d0a7fc3f6e5634e32c36456e2840308911f3c9beadbd129fc4bd4f653aaeeaae`;
the stage ledger has SHA-256
`e1bdd1fddeba66945ca6db2204aca17a8a7bfde62b953545bb848a9687e339b8`.
The internal `SHA256SUMS` manifest was independently rechecked and matched all
13 recorded files.

This seal is the **overlap/Schur reduction**, not physical attainment of
window 15 and not a terminal producer.  The live counters remain exactly
`20/41` and `TermSource = 0`.  The next source-specific obligation is to
decide whether the displayed majorant can satisfy its own scalar premise; a
failure of that majorant would not imply `norm R' >= 1` for the physical
operator.

### Diagonal step-7 majorant no-go (SEALED; physical contraction not refuted)

Checkpoint `8494a73fcf1e6fc2bb59ab6442e7631cfcfe94a0` proves that the
particular one-parameter generated Combes--Thomas/Schur majorant used by the
sealed step-7 reduction cannot satisfy its own `< 1` premise already at
depth zero when `M >= 2` and the spacing is positive.  The proof derives
`3 <= derivBound`, exposes the exact depth-zero generated coercivity, and
gives the explicit (inessential) lower bound `11943936` for that majorant.

Cold GitHub Actions run `31034176002` (workflow checkpoint `85e787fc`) set
`COLD_MODE=true`, restored no project `.lake/build` cache, and compiled the
focal with `Build completed successfully (8569 jobs).`  The four-declaration
audit exited zero and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.  The gate recorded
`FINAL_STATUS=PASS` against Mathlib
`07642720480157414db592fa85b626dafb71355b` and the official Lean
`v4.29.0-rc6` asset.

The deterministic evidence archive has SHA-256
`2c569535f50d50c1864be0287253adfe8554e32776efd288368fb9e9e16ebd7b`.
The axiom JSON has SHA-256
`6ee8ef575065609b28fc399f5b580fc2a70da078df0ecf65c6f611c0a7121741`;
the stage ledger has SHA-256
`c12115adf80030df05f9303fe5cfe8d69082b9793cdeb72003223ef50b9da366`.
The internal `SHA256SUMS` manifest was independently rechecked and matched all
13 recorded files.

This is a no-go for the **majorant**, not for the physical defect operator:
it proves neither `1 <= norm R'` nor failure of the printed CMP99
contraction.  The obstruction comes from identifying the RG block ratio with
the source's independently large regional parameter.  The partition/cutoff
infrastructure for the source-faithful replacement keeps the generated tower
and its Poincare cost at fixed ratio `L`, introduces a separate regional
parameter `K`, and proves the exact cutoff gain `4 * derivBound / K` before
any layer sum.  Its active-cell theorem has the same bound `16` for every
`K`.  These facts are inputs to, not substitutes for, a direct formalization
of CMP99 (3.89).  Reassembling another CT + Schur majorant is not an accepted
repair of step 7.  The later CMP99 Theorem-3.15 condition coupling
the printed large parameter to `alpha_0` remains a separate covariance/source
dictionary obligation.  Window 15 therefore remains open, and the live
counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4f signed cutoff-Laplacian Green/overlap endpoint (SEALED; third species open)

Exact source checkpoint `d8094af41c78851d8b985b2f7e1550857531202f`
passed cold GitHub Actions run `31085829837` (workflow checkpoint
`8e94f9de8ac0b5ed2c90f01b3428cba29fcbfaea`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
compiled the focal from `2026-08-06T08:41:48Z` to `09:44:15Z`.  The audit
finished at `09:44:28Z`; both stages exited zero.  All eight audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The brick transports the value component of the literal CMP99 (3.42)
regional-Green certificate through restriction and zero extension, composes
it with the signed source-separated cutoff-Laplacian coefficient, and proves
the exact pre-overlap amplitude

`12 * B0 * secondDerivBound / Klarge^2`.

The two powers of the generated Green scale cancel before any family sum.
The right signed cutoff then restricts the cell sum at each source, so the
already sealed geometric overlap contributes exactly `16`, independent of
`Klarge` and of the total number of cells.  The operator is identified with
the literal cutoff-Laplacian species of CMP99 (3.88); no CT + Schur majorant
or reciprocal coercivity constant enters the estimate.

The independently downloaded deterministic evidence archive has SHA-256
`1741117ef8b72e4b8f782564e7224ac0a7caa89a5e7c982022be8354007a57c5`.
Its axiom JSON has SHA-256
`385f608fe631b430cfeaaf0ce65b1ae011027329d10f835a54439aa9ea14ff92`;
the stage ledger has SHA-256
`69e996f2c372a6f5ab3c02384e19c168bfa06fb132dd335c25081905ea21e1e3`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This completes the signed second species and its overlap sum only.  The
normalized `Q'^*Q'` third species with varying Green values, the complete
three-species CMP99 (3.89) estimate, `norm R' < 1`, rows 23--24, and a
`TermSource` inhabitant remain open.  Window 15 is compatible but unattained;
the live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4g terminal-fibre varying-value normalization (SEALED; Green/third species open)

Exact source checkpoint `87e5f54efacfdccac6513024e6e44e5c41d184b8`
passed cold GitHub Actions run `31092556326` (workflow checkpoint
`718f69da445a13abb4d81caca838b7eb9e174c9a`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
compiled the focal from `2026-08-06T10:18:09Z` to `10:38:32Z`.  The audit
finished at `10:38:39Z`; both stages exited zero.  One audited declaration
uses only `[propext]`; the other four use exactly
`[propext, Classical.choice, Quot.sound]`.

The brick proves the source-faithful varying-value estimate for the literal
generated counting mass.  Outside the actual `SameTerminalBlock` fibre every
kernel block vanishes exactly.  Inside it, each block has norm
`(L^-4)^(2*r) * norm(phi source)`, while the fibre contains at most
`L^(4*r)` sites.  The exact cancellation therefore leaves one and only one
normalized factor `(L^-4)^r`, before any regional-cell or layer sum.  No
range-ball cardinality, abstract adjoint-orientation transport, or bound on
`phi` outside the terminal fibre is introduced.

The independently downloaded deterministic evidence archive has SHA-256
`5a71078c26c371c4a05449993d170bd2bdc1db5dd3fd3dbff766e0827e72bee5`.
Its axiom JSON has SHA-256
`08cdb34aa8931541162079ce52476a9e64287d71a16831c1ba855335f5e58946`;
the stage ledger has SHA-256
`e8e5897ce0f0ae502d4e08967cad2bd35f85c395ce6317f85e600707e61c31ad`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This is the terminal-fibre normalization input only.  The exact reindexing
to the separated ambient carrier, equality of the CMP99 (3.42) regional
metric across one terminal fibre, insertion of the varying regional Green
values and signed cutoff difference, the complete third species, full
CMP99 (3.89), `norm R' < 1`, rows 23--24, and a `TermSource` inhabitant
remain open.  Window 15 is compatible but unattained; the live counters
remain exactly `20/41` and `TermSource = 0`.

### Step 7.4h generated-mass common metric (SEALED; Green insertion open)

Exact source checkpoint `9d563cdd910276de19787e6f62e0733fe6cd975c`
passed cold GitHub Actions run `31095036070` (workflow checkpoint
`a98105c8128e17a3e7da8d612f7c94e9ca011f46`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
compiled the focal from `2026-08-06T10:55:24Z` to `11:14:03Z`.  The audit
finished at `11:14:09Z`; both stages exited zero.  All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The brick proves two exact transports needed by the normalized third
species.  First, a varying-coordinate fixed-output norm sum is invariant
under isometric reindexing of both kernel legs.  Second, equality of the
literal generated `L^(depth+1)` terminal owner implies equality of the
larger separated `K * L^(depth+1)` Green owner.  Hence the printed CMP99
(3.42) block metric is exactly constant across one terminal fibre, with no
extra `exp(delta0)` factor and no cardinality estimate.

The independently downloaded deterministic evidence archive has SHA-256
`798658975077470bdad004fe99bcb49e23a9e3d7f27fffe5c323bb18ab4a68eb`.
Its axiom JSON has SHA-256
`8bf10186cdd9c1d026ce36ea5f75e6bb247bbc0c0ab6452e53bbc2ebb2551686`;
the stage ledger has SHA-256
`fdfcacba9335e99cbbdebfe8cbb311881e765966d0ecc8b6e84b2b1fd48556ad`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This is geometry and reindexing infrastructure only.  It does not insert the
regional Green bound, multiply by the signed cutoff difference or normalized
mass coefficient, sum cells, prove the complete third species or full CMP99
(3.89), attain `norm R' < 1`, discharge rows 23--24, or inhabit a
`TermSource`.  Window 15 remains compatible but unattained; the live
counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4i generated-mass Green/cutoff insertion (SEALED; ambient third-species assembly open)

Exact source checkpoint `c44d8c2a146ef1eaf9aeab6d8edd00046f47a4c5`
passed cold GitHub Actions run `31097908966` (workflow checkpoint
`10d8b4464be3347e9e949adeb0d076ae9e8ade83`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
compiled the focal from `2026-08-06T11:38:18Z` to `12:39:21Z`.  The audit
finished at `12:39:31Z`; both stages exited zero.  All four audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The brick inserts two physical values into the normalized generated-mass
estimate.  The diameter of one terminal fibre multiplied by the signed
cutoff slope leaves the explicit factor `8 * derivBound / K`.  The regional
Green value is evaluated with the one common CMP99 (3.42) metric proved in
Step 7.4h.  Their product is then consumed by the literal generated counting
mass with exactly one surviving normalized block weight.

The independently downloaded deterministic evidence archive has SHA-256
`df455019d5d906e738632963c65b4c8a635197a4707c46b7ad6c9cf3e2f51977`.
Its axiom JSON has SHA-256
`c8e0e5538fe846684f310aa35ea783ca11d665f4f4472b971000e19d0cd5e158`;
the stage ledger has SHA-256
`d53b34a1e120de5cdc200dd18f4f522934546bc8150f406be825513f779f9968`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This is still infrastructure below the complete physical third species.  It
does not prove the separated ambient mass reindexing, install the literal
physical scalar mass `cmp99SourceGeneratedPhysicalMass`, sum cells, prove the
complete third species or full CMP99 (3.89), attain `norm R' < 1`, discharge
rows 23--24, or inhabit a `TermSource`.  Window 15 remains compatible but
unattained; the live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4j separated ambient generated-mass atom (SEALED; right cutoff/cell sum open)

Exact source checkpoint `c221f73c2f48dba9e018752f9fb1813c039fc0e6`
passed cold GitHub Actions run `31104001016` (workflow checkpoint
`99d3082cf6d5d68b678f71fdd17f7df4d602830c`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
compiled the focal from `2026-08-06T13:03:52Z` to `13:53:49Z`.  The audit
finished at `13:54:03Z`; both stages exited zero.  All four audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The brick reindexes the literal generated counting mass from its active
carrier to the separated ambient carrier and installs the literal physical
scalar `cmp99SourceGeneratedPhysicalMass`.  The sign is fixed by the printed
commutator orientation: the varying-value helper uses
`h(source) - h(target)`, while the physical atom restores
`h(target) - h(source)`.  The endpoint keeps the absolute physical mass and
the single surviving normalized block-average weight as distinct factors.

The independently downloaded deterministic evidence archive has SHA-256
`6c364157fade4ff397ef724f11cb7a23dd5434ef1e15ba4e06e03ba072d26183`.
Its axiom JSON has SHA-256
`2bff87eb358793668e11f86316917522270d59aa8c428b088f695ad5e88ebc9b`;
the stage ledger has SHA-256
`331f6d3c3d6fceb0b2d52db7e821917680d8df8132058287291165ba61319753`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This seals the separated ambient mass atom before the contractive right
cutoff.  It does not sum the atom to the literal commutator operator, insert
the right cutoff, sum regional cells, prove the complete third species or
full CMP99 (3.89), attain `norm R' < 1`, discharge rows 23--24, or inhabit a
`TermSource`.  Window 15 remains compatible but unattained; the live counters
remain exactly `20/41` and `TermSource = 0`.

### Step 7.4k complete generated-mass species (SEALED; three-species assembly open)

Exact source checkpoint `050783b4155282d06df25c4566fc125fa9463d4a`
passed cold GitHub Actions run `31113901772` (workflow checkpoint
`2b961a2d8b28c42ae25eab05f5c86ef80cd8b0ee`).  The run recorded
`COLD_MODE=true`, restored and saved no project `.lake/build` cache, and
compiled the focal from `2026-08-06T15:11:42Z` to `15:57:14Z`.  The audit
finished at `15:57:34Z`; both stages exited zero.  All nine audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The brick assembles the literal generated-mass commutator on the separated
ambient carrier, inserts the canonical regional Dirichlet Green and the
contractive right signed cutoff, and sums all cells using exactly the sealed
source overlap `16`.  The pre-overlap budget keeps the physical scalar mass,
the one surviving normalized counting-mass weight, the signed cutoff gain
`8 * derivBound / K`, and the Green amplitude as separate visible factors.
No cardinality `K^4`, generic Schur conversion, Poincare constant or shared
three-species constant is introduced.

The independently downloaded deterministic evidence archive has SHA-256
`6467cf2c1d01589853d01aec874610bc7bab01d5e181d98317462f3d6e372dd6`.
Its axiom JSON has SHA-256
`1e77889f1ba6f1ba04ae922409ca01971167e0b6574da8142bcc6d57858ff9ac`;
the stage ledger has SHA-256
`b99e9f557de665dcb257b7aeef82980baba5bcf8ee0297c3a017c15e924eb302`.
All 13 entries of the internal `SHA256SUMS` manifest independently matched.

This seal completes only the third displayed species of CMP99 (3.89).  The
first species still requires its signed-cutoff reinstantiation; the literal
sum of all three species, defect contraction, rows 23--24 and a `TermSource`
inhabitant remain open.  Window 15 remains compatible but unattained; the
live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4l signed covariant-link first species (SEALED; three-species assembly open)

Exact source checkpoint `46734245d55a2ae309a01e6b371b35418189dd0f`
passed a cold Colab Pro+ CPU/high-RAM clone opened at
`2026-08-06T23:56:13.069777Z`.  The runner checkpoint was
`2a9f0d998ab8246d5addd878a08c4208cfc438bd` and the notebook checkpoint was
`12e8d03b2920a7373ae9d9d1bc13f4409667174c`.  The focal exited zero after
`5154.941` seconds with the literal terminal line
`Build completed successfully (8574 jobs).`; the audit exited zero after
`30.721` seconds.  All fifteen audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The gate recorded
`FINAL_STATUS=PASS` against Mathlib
`07642720480157414db592fa85b626dafb71355b` and Lean `v4.29.0-rc6`, then
automatically released the runtime.

The deterministic evidence payload generated in Colab has SHA-256
`9c7edd207174abb76cf2fac4296ffd480bae6c579fc366d3246250232a323a3a`;
the generated archive has SHA-256
`4d28f76efcb91effb81fb6448ce1970e78ea12278dc3ad5b24712ff47161956c`.
These digests are transcript-visible runner outputs; this seal does not claim
an independent Windows download or rehash of the archive.

The brick reconstructs the first covariant-link species from the exact
ambient product rule using the source-faithful signed cutoff.  Its source
budget keeps the signed cutoff gain `8 * derivBound / K` visible before the
cell sum, and the contractive right cutoff uses exactly the already sealed
geometric overlap `16`.  The covariant-link contribution remains separate
from the normalized generated-mass contribution: no shared three-species
constant, generic row/column symmetry, Combes--Thomas/Schur majorant, or
Poincare constant is introduced.

The preceding v5 diagnostic at source checkpoint
`c0f892e86288b3e2778dcc44dbdc33f38b78219a` failed only at two endpoint
inference timeouts; its evidence and archive SHA-256 digests were respectively
`c3d8b5dcbafb147b5800fcf1c6e4a9648ecae41c1bc95b5e3f160b1d3691fead`
and `86ae7f66c613614df27b0d3ce87824756e8482cd8745ae0555a3896c436f1b50`.
The repair pinned the physical carrier and fibre in the two conclusions; it
did not change a theorem, constant, hypothesis, or heartbeat.

All three displayed species now have separate cold seals, but their literal
three-species assembly is still open.  This brick does not prove complete
CMP99 (3.89), the defect contraction `norm R' < 1`, rows 23--24, or a
`TermSource` inhabitant.  Window 15 remains compatible but unattained; the
live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.4m coarse-cell coordinate-probe three-species assembly (SEALED; source-facing (3.89) open)

Exact source checkpoint `437a4edf584d19abf4df93c3c24cb5e584ccba5e`
passed cold GitHub Actions run `31143972802` (workflow checkpoint
`5064ebd73c0578cb732597252396ff0af016e4d4`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T03:20:59Z` to `04:23:04Z` and exited zero;
the audit ended at `04:23:22Z` with exit zero.  All nine audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The brick constructs one dependent reindexing of the fine physical
background, one generated precision and one coercivity witness, then adds the
three separately sealed species with their budgets still visible.  This
closes the literal operator algebra and its coordinate-probe exponential
bound on the separated-cell metric.

It does **not** close the printed CMP99 (3.89) estimate.  The sealed predicate
tests `singleFinitePiLp source v`, whereas the source quantifies an arbitrary
field supported in one localization block and measures it in the finite sup
norm.  Its metric divisor is `K * L^(depth+1)`, whereas the source metric is
at scale `L^(depth+1)` on the `2*(K*Q)` localization carrier.  A generic sum
over coordinate probes is not accepted because its fine-fibre cardinality
can erase the physical `K^-1` gain.  The next source-facing brick must expose
those two quantifiers directly.  Hence window 15 remains compatible but
unattained, the live producer count remains exactly `20/41`, and
`TermSource = 0`.

### Step 7.5a block-localized sup-norm action contract (SEALED; physical producer open)

Exact source checkpoint `16eed86994e2459bacb765e193c5009b76fdd51c`
passed cold GitHub Actions run `31147882660` (workflow checkpoint
`6de2a6f96b72a4863a486b02bb620b0d67743efc`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T04:37:09Z` to `04:38:36Z` and exited zero;
the audit ended at `04:38:43Z` with exit zero.  All six audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The new predicate quantifies an arbitrary finite field supported in one
source-owner fibre, uses its finite supremum norm, and measures decay between
explicit source and target owners.  Its addition lemma preserves the sum of
amplitudes with no site-cardinality factor.  It is therefore the correct
generic codomain for the source-facing CMP99 (3.42)/(3.89) estimates, rather
than an entrywise coordinate-probe predicate.

This brick defines and verifies only the contract.  It does not prove that
the regional Green components or the physical three-species defect satisfy
it, and it does not identify the source localization owners at scale
`L^(depth+1)` with the existing separated-cell presentation.  Complete
CMP99 (3.89), `norm R' < 1`, rows 23--24, and a `TermSource` inhabitant remain
open.  Window 15 is compatible but unattained; the live counters remain
exactly `20/41` and `TermSource = 0`.

### Step 7.5b source localization-owner dictionary (SEALED; Green estimates open)

Exact source checkpoint `fd070233dbeaf13ad2d59acfc5295ff76900d86d`
passed cold GitHub Actions run `31148630489` (workflow checkpoint
`b94804c37c0e2f23d1dcc3dd9126ae68f2f71b0d`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T04:51:47Z` to `05:19:01Z`, exited zero, and
ended with `Build completed successfully (8517 jobs).`  The audit ended at
`05:19:06Z` with exit zero.  Its five declarations use only the allowed
axioms: one uses `[propext]` and four use exactly
`[propext, Classical.choice, Quot.sound]`.

The brick proves the exact carrier equality between the separated regional
presentation and the `L^(depth+1)` source-localization presentation, builds
the corresponding explicit site equivalence, and defines the owner and
owner-distance used by the printed CMP99 (3.89) estimate.  It specializes
the sealed block-localized sup-norm contract to those owners without
hard-coding the depth.

This is carrier and metric bookkeeping only.  It does **not** prove any
regional-Green localized-action estimate, the physical three-species form of
CMP99 (3.89), `norm R' < 1`, rows 23--24, or a `TermSource` inhabitant.
Window 15 remains compatible but unattained; the live counters remain
exactly `20/41` and `TermSource = 0`.

### Step 7.5c source-localized CMP99 (3.42) Green certificate (SEALED; (3.89) open)

Exact source checkpoint `39bf5a9a5978aa52fe6d05a4d057206a027d6af5`
passed cold GitHub Actions run `31158229361` (workflow checkpoint
`6d3939b2e164d5f8ee10d2e86e1efe3b2d631710`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T07:36:57Z` to `08:03:14Z`, exited zero, and
ended with `Build completed successfully (8519 jobs).`  The audit ended at
`08:03:24Z` with exit zero.  All nine audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The certificate fixes one canonical regional Dirichlet Green and records the
four source estimates printed in CMP99 (3.42): `G'`, `D G'`, `G' D*`, and
`Delta G'`, with scale vector `[B0*ell^2, B0*ell, B0*ell, B0]`,
`ell = L^(depth+1)`, and the sealed source-localization owner metric.  Its
strictly positive `B0` and `delta0` and its active-carrier nonemptiness are
visible in the type; it does not accept an arbitrary Green family.

This is a named source certificate for (3.42), not a proof of that theorem
from CMP99.  It proves neither the physical three-species estimate (3.89),
the defect contraction, rows 23--24, nor a `TermSource` inhabitant.  Window
15 remains compatible but unattained; the live counters remain exactly
`20/41` and `TermSource = 0`.

### Step 7.5d block-localized supremum algebra (SEALED; physical species open)

Exact source checkpoint `34d70c000e7a0f5836a5c983a38528e9459f62ed`
passed cold GitHub Actions run `31160962546` (workflow checkpoint
`9a580feaa362ce59d8cbd69c21e0801de2514904`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T08:17:38Z` to `08:35:59Z`, exited zero, and
ended with `Build completed successfully (8441 jobs).`  The audit ended at
`08:36:11Z` with exit zero.  All ten audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The brick proves directly in the source supremum norm that contractive
source multipliers preserve an owner fibre and its norm, bounded target
multipliers change only the displayed amplitude, and regional restriction
and zero extension preserve the literal ambient owner metric.  No expansion
into coordinate probes or fine-fibre cardinality occurs.

This is exact norm/support algebra below (3.89), not a physical species
estimate.  It proves neither the three-species bound, the defect contraction,
rows 23--24, nor a `TermSource` inhabitant.  Window 15 remains compatible but
unattained; the live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.5e source-localized second species (SEALED; overlap and other species open)

Exact source checkpoint `8c5f917c2887fd85bec4b0ca2c3d82823fab037c`
passed cold GitHub Actions run `31162995186` (workflow checkpoint
`da14ec7652726b262f647e906dfe79b830657c81`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T08:47:11Z` to `09:31:25Z`, exited zero, and
ended with `Build completed successfully (8571 jobs).`  The audit ended at
`09:31:30Z` with exit zero.  Its declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

The theorem applies the literal signed right cutoff, one canonical regional
Dirichlet Green from the sealed source certificate, and the literal signed
cutoff-Laplacian coefficient.  It quantifies an arbitrary field supported in
one source owner fibre and retains the exact pre-overlap amplitude
`12 * B0 * secondDerivBound / K^2`, with no coordinate-probe expansion.

This is one physical regional cell of the second species.  The overlap-16
cell sum, first and third source-localized species, complete (3.89), defect
contraction, rows 23--24, and a `TermSource` inhabitant remain open.  Window
15 remains compatible but unattained; the live counters remain exactly
`20/41` and `TermSource = 0`.

### Step 7.5f source-localized first species (SEALED; overlap and complete (3.89) open)

Exact source checkpoint `c1b6db9a3c972afac0337677787d7feb7d7a9696`
passed cold GitHub Actions run `31167654134` (workflow checkpoint
`3bda3465eaf26fc52dde0d678e4f61bf469ac9bd`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T09:54:14Z` to `10:56:06Z`, exited zero, and
ended with `Build completed successfully (8579 jobs).`  The audit ended at
`10:56:12Z` with exit zero.  Both declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The theorem applies the literal left-derivative Green estimate of CMP99
(3.42) to an arbitrary field supported in one source-owner fibre, then uses
the exact signed-cutoff slope and one-step owner geometry.  It retains the
visible `K^-1` gain before cell summation and introduces neither coordinate
probes, a Schur estimate, nor reciprocal coercivity.

This is one physical regional cell of the first species.  The overlap-16
cell sum, the source-localized third species, complete (3.89), contraction,
rows 23--24, and a `TermSource` inhabitant remain open.  Window 15 remains
compatible but unattained; the live counters remain exactly `20/41` and
`TermSource = 0`.

### Step 7.5g source-localized third species (SEALED; overlap and complete (3.89) open)

Exact source checkpoint `f8e7b3f2dde8ab286232580f1a69107a4afb5a6e`
passed cold GitHub Actions run `31174809660` (workflow checkpoint
`45ef1e3f57a6cbd8471dc80d2d72b7411c0cf614`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T11:38:59Z` to `12:39:56Z`, exited zero, and
ended with `Build completed successfully (8579 jobs).`  The audit ended at
`12:40:06Z` with exit zero.  All four declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The theorem applies the literal generated counting-mass species to an
arbitrary field supported in one source-owner fibre.  The generated terminal
fibre preserves that owner exactly, so the normalized counting-mass estimate
retains its source metric and introduces neither a coordinate-probe expansion
nor an ambient/fine-fibre cardinality loss.

This is one physical regional cell of the third species.  The overlap-16
cell sum, the three-species assembly, complete (3.89), defect contraction,
rows 23--24, and a `TermSource` inhabitant remain open.  Window 15 remains
compatible but unattained; the live counters remain exactly `20/41` and
`TermSource = 0`.

### Step 7.5h source-localized regional defect (SEALED; global contraction open)

Exact source checkpoint `a814d95ac5bb20fa8bfe8871e8764caf2353153b`
passed cold GitHub Actions run `31180210309` (workflow checkpoint
`c0f037231b554b7d55b9cbb8b771bd799067d4b7`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The four focal/audit pairs all exited zero.  Their focal endpoints were
`Build completed successfully (8523 jobs).`, `(8173 jobs).`, `(8590 jobs).`,
and `(8593 jobs).`; all fourteen audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed chain constructs the source-owner geometry, proves the overlap-16
localized-action sum, assembles all three literal CMP99 (3.88) species on the
same generated background, and obtains the complete source-localized regional
defect bound.  The estimate acts on an arbitrary field supported in one
source-owner fibre and introduces neither the number of fine sites nor the
number of owners.

This is still a source-localized single-application estimate, not a global
operator-norm contraction.  The complete amplitude contains the visible
first- and third-species `K^-1` terms as well as the second-species `K^-2`
term.  Iteration at a fixed exponential rate still requires a positive rate
gap and a volume-uniform shell convolution bound.  No Neumann inverse,
attainment of window 15, rows 23--24, or `TermSource` inhabitant is proved.
The live counters remain exactly `20/41` and `TermSource = 0`.

### Step 7.5i one-application global supremum bound (SEALED; fixed-rate powers open)

Exact source checkpoint `49721e8e244fc1aaff93e5881e89483155431301`
passed cold GitHub Actions run `31187878878` (workflow checkpoint
`81ee5ec95d2ba1135937147683bb1a27472dc5f2`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The generic focal ran from `2026-08-07T14:42:31Z` to `14:59:38Z`, and the
physical focal from `14:59:48Z` to `15:42:22Z`; all four focal/audit stages
exited zero.  The six generic and two physical audit blocks use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed theorem decomposes an arbitrary field into exact source-owner
fibres and uses the volume-uniform four-dimensional owner-shell sum to bound
one application of the literal regional defect in `finitePiLpSupNorm`.  No
number of owners and no fine-fibre cardinality enters.  Its budget keeps the
two physical `K^-1` contributions and the `K^-2` contribution visible before
multiplication by the shell sum.

This is not yet the source-faithful Neumann contraction.  Fixed-rate powers
require a block-operator coefficient matrix with an output-fixed weighted
owner row and a strict reserved rate `0 <= r < delta0`; the coordinate-delta
weighted-row predicate is not an admissible substitute because it would
reintroduce fine-fibre cardinality.  The Green certificate still supplies
`B0` and `delta0` at the selected `K`, so scalar large-`K` compatibility alone
does not manufacture their required physical uniformity.  Window 15 remains
compatible but unattained; rows 23--24 remain open, the live producer count
is `20/41`, and `TermSource = 0`.

### Step 7.5j output-fixed weighted owner row (SEALED; powers open)

Exact source checkpoint `596802620b489c55a9a34c0e445323c1f426a125`
passed cold GitHub Actions run `31195176692` (workflow checkpoint
`f117f7f7b8cea4c3a93e41bd6b8dd2795f5a1f30`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The generic focal ran from `2026-08-07T15:59:09Z` to `16:17:23Z`, and the
physical focal from `16:17:31Z` to `17:05:09Z`; all four focal/audit stages
exited zero.  The seven generic and three physical audit blocks use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed interface exposes a nonnegative scalar matrix of supremum-action
bounds between complete owner fibres.  Its spatial norm fixes an output owner
and sums source owners with weight `exp(rate * dist)`, the orientation needed
by the global supremum norm.  The physical CMP99 specialization derives that
row at every `0 <= rate < delta0`, with literal amplitude
`16 * threeSpeciesBudget * cmp99OmegaSiteExpSumBound (delta0 - rate)`.
Neither the number of owner blocks nor a fine coordinate cardinality enters.

The first two attempted workflow vehicles failed before Lean: one pinned a
nonexistent expanded SHA and one exceeded the cache action's ten-key limit.
They are instrumentation incidents, not mathematical evidence.  Cached run
`31194902046` then passed, but PRE-VALIDATION was retired only after the cold
run above.

This brick fixes the correct Banach norm and rate reserve but proves no
submultiplicativity, power bound, Neumann inverse, or strict budget.  The
literal amplitude still contains two `K^-1` species and one `K^-2` species;
the Green certificate supplies `B0` and `delta0` at the selected `K` rather
than producing their uniformity.  Window 15 remains compatible but
unattained; rows 23--24 remain open, the live count is `20/41`, and
`TermSource = 0`.

### Step 7.5k owner-weighted kernel composition (SEALED; powers open)

Exact source checkpoint `c53f7dcb7ecdcde84570c92041d1e01505a8f3ad`
passed cold GitHub Actions run `31202378080` (workflow checkpoint
`e1f1f314ce31aaefbebbd3a7d1323d59a098a9b9`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T17:29:28Z` to `17:46:09Z` and ended with
`Build completed successfully (8444 jobs).`; the audit ended at `17:46:17Z`.
Both stages exited zero, and all six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed algebra decomposes an intermediate field into complete owner
fibres, composes the explicit nonnegative block coefficients by literal
matrix convolution, and proves that output-fixed weighted rows are
submultiplicative at the same reserved rate.  The proof uses only the owner
distance triangle inequality.  It introduces neither an owner-cardinality
factor nor a fine-coordinate expansion.

Run `31201201776` stopped before Lean because the cache action received eleven
keys, above its limit of ten.  Run `31201285673` then exposed an over-broad
rewrite of the owner decomposition; the source was repaired with a directed
`congrArg`.  Cached diagnostic run `31202127234` passed, but PRE-VALIDATION
was retired only after the cold run above.

This brick proves composition, not coefficient powers, a Neumann inverse, or
the strict physical budget.  In particular it does not manufacture uniform
`B0` or `delta0` as `K` varies.  Window 15 remains compatible but unattained;
rows 23--24 remain open, the live count is `20/41`, and `TermSource = 0`.

### Step 7.5l fixed-rate owner-kernel powers (SEALED; Neumann sum open)

Exact source checkpoint `be228322bea6ec973369001575f5780f9840f92f`
passed cold GitHub Actions run `31206356093` (workflow checkpoint
`648024c344673f4efd4daf1fc1e878c7caef8b0a`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T18:20:55Z` to `18:39:22Z` and ended with
`Build completed successfully (8445 jobs).`; the audit ended at `18:39:31Z`.
Both stages exited zero, and all seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick constructs the literal diagonal coefficient for the identity
operator and the convolution powers of an arbitrary nonnegative owner kernel.
The composition theorem from Step 7.5k then proves by induction that every
operator power retains the same output-fixed spatial rate and has exact
geometric amplitude `A ^ n`.  No owner-cardinality factor and no rate loss are
introduced.

Runs `31204627351` and `31205040141` exposed only elaboration defects in the
identity layer; cached run `31206078448` passed.  Run `31205417982` was
cancelled as an infrastructure stall before Lean after more than twice the
dependency-materialization prior.  PRE-VALIDATION was retired only after the
cold run above and local verification of its durable evidence package.

This brick does not form or sum the Neumann series, prove `A < 1`, specialize
the physical CMP99 amplitude, or produce uniform `B0` and `delta0` as `K`
varies.  Window 15 remains compatible but unattained; rows 23--24 remain open,
the live count is `20/41`, and `TermSource = 0`.

### Step 7.5m owner-sup contraction implies power summability (SEALED; Neumann identities open)

Exact source checkpoint `816fd138ff952be7bab1105b7b0e11c175d88cca`
passed cold GitHub Actions run `31208946899` (workflow checkpoint
`992bc3d967c6898fbd287c3425cacd8701b27090`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T18:54:35Z` to `19:10:40Z` and ended with
`Build completed successfully (8446 jobs).`; the audit ended at `19:10:47Z`.
Both stages exited zero, and all six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed bridge first proves that an output-fixed weighted owner row bounds
one global finite-supremum application with no owner or fibre cardinality.
Every operator power therefore has ratio `A ^ n` at the same spatial rate.
The explicit factor `sqrt(card ι)` enters only in the finite-dimensional
comparison from this supremum norm to the existing counting-L2 topology; it
is a fixed convergence prefactor, not part of the physical row amplitude.
Consequently `A < 1` makes `Summable (fun n => T ^ n)` in the continuous
linear-map space.

Cached diagnostic run `31208721237` passed on the first source attempt.
PRE-VALIDATION was retired only after the cold run and local verification of
the downloaded evidence package.

This brick proves convergence, not the value of the `tsum`, its left/right
inverse identities, the strict physical CMP99 amplitude, or uniform
production of `B0` and `delta0` as `K` varies.  Window 15 remains compatible
but unattained; rows 23--24 remain open, the live count is `20/41`, and
`TermSource = 0`.

### Step 7.5n owner-weighted Neumann `tsum` and fixed-rate bound (SEALED; inverse identities open)

Exact source checkpoint `9ff84c7b54f89ce860a3c4690e60ac9684b886d4`
passed cold GitHub Actions run `31211383877` (workflow checkpoint
`7a445d712556ac1076ff354752c3200b7ab6412a`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T19:27:25Z` to `19:40:05Z` and ended with
`Build completed successfully (8447 jobs).`; the audit ended at `19:40:13Z`.
Both stages exited zero, and all seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick forms the literal operator and coefficient `tsum`s.  It
proves that the coefficient is nonnegative and that the Neumann operator has
output-fixed weighted owner row at most `(1 - A)⁻¹` at the unchanged spatial
rate.  No owner-cardinality factor and no loss of rate enter the physical
owner-sup bound.

Cached diagnostic run `31211060902` passed after run `31210795917` exposed
one elaboration ambiguity in the weighted finite sum.  Run `31210716821`
stopped before Lean because the cache action received too many restore keys.
PRE-VALIDATION was retired only after the cold run above and local
verification of its durable evidence package.

This brick does not prove the left or right inverse identity for the `tsum`,
specialize the strict physical CMP99 amplitude, or produce uniform `B0` and
`delta0` as `K` varies.  Window 15 remains compatible but unattained; rows
23--24 remain open, the live count is `20/41`, and `TermSource = 0`.

### Step 7.5o two-sided owner-weighted Neumann inverse (SEALED; physical contraction open)

Exact source checkpoint `da5a4d257b4bac5d025e500157af83957e8f8f40`
passed cold GitHub Actions run `31213231725` (workflow checkpoint
`28141ebaea5383d21071bab78734ee7377470c89`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T19:56:33Z` to `20:08:31Z` and ended with
`Build completed successfully (8448 jobs).`; the audit ended at `20:08:36Z`.
Both stages exited zero, and both audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed ring-level bridge applies the telescoping theorem for a summable
geometric series to the already certified owner-weighted power sum.  It proves
both `(sum T^n) * (1 - T) = 1` and `(1 - T) * (sum T^n) = 1` for the literal
continuous-linear-map `tsum`; no extra norm comparison, owner count, or rate
loss is introduced.

Run `31212939832` stopped before Lean because the cache action counts the
primary key inside its maximum of ten.  The restore list was capped without
changing source, and cached diagnostic run `31213016266` then passed.
The runner now derives the fallbacks from one prefix list and rejects
`primary + fallbacks > 10` before invoking `actions/cache`.
PRE-VALIDATION was retired only after the cold run above and local
verification of its durable evidence package.

This brick does not prove that the physical CMP99 defect has amplitude below
one or produce uniform `B0` and `delta0` as `K` varies.  In particular it does
not supply the dominant `K^-1` coefficient or the one-time conversion factor
`S(delta0 - r)`.  Window 15 remains compatible but unattained; rows 23--24
remain open, the live count is `20/41`, and `TermSource = 0`.

### Step 7.5p exact physical large-block scale (SEALED; physical contraction open)

Exact source checkpoint `c4a33843f9081d537c61d157a47f94be699a77aa`
passed cold GitHub Actions run `31216957809` (workflow checkpoint
`5c00b66a9ed3f3b50275e0a554d9455239f0d94b`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T20:43:51Z` to `21:30:35Z` and ended with
`Build completed successfully (8598 jobs).`; the audit ended at `21:30:43Z`.
Both stages exited zero, and all five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed source-level equality rewrites the literal physical CMP99 (3.89)
output-fixed owner-row budget as

```text
leadingNumerator / K + quadraticNumerator / K^2.
```

The two first-order species remain visibly separate inside
`leadingNumerator`; the cutoff-Laplacian species is the quadratic numerator.
Thus the available large-block gain is dominated by `K^-1`, not `K^-2`.
The conversion from source decay `delta0` to the owner-weighted rate pays
`cmp99OmegaSiteExpSumBound (delta0 - rate)` exactly once, before Neumann
composition.  The currently formalized shell bound counts balls
`(2*n+1)^4`, hence has small-rate order `(delta0-rate)^-5`; the sharper
`^-4` layer asymptotic is not claimed by this brick.

The scalar lemma proves only that, for fixed nonnegative numerators, some
natural `K >= 2` makes `a1/K + a2/K^2 < 1`.  It does not construct a family
of physical Green certificates whose `B0` and `delta0` are uniform as `K`
varies.  It also leaves visible the independent source gate from CMP99
Theorem 3.15: the printed large-block parameter times `alpha_0` must remain
sufficiently small.  Therefore increasing `K` has no formal upper bound in
the combinatorial overlap geometry, but for fixed `alpha_0` the source gate
does impose an upper scale; compatibility requires co-tuning `alpha_0`
downward (or extracting a stronger source theorem).  No numerical threshold
for that gate has yet been extracted from the primary text.

Consequently this brick does not attain window 15, discharge rows 23--24,
or inhabit a `TermSource`.  The live count remains exactly `20/41`, and
`TermSource = 0`.

### Step 7.5q exact source-input L2 scale for CMP99 (3.42) (SEALED; Green estimates open)

Exact source checkpoint `d1c9e8585d0496fe283260d9b92447c3b3271ac4`
passed cold GitHub Actions run `31221718782` (workflow checkpoint
`e542e12b5f4a1fdd514a156dd49af491ddf28fcf`).  The run recorded
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran from `2026-08-07T21:54:24Z` to `22:21:36Z`, exited zero, and
ended with `Build completed successfully (8520 jobs).`; the audit ended at
`22:21:43Z`.  All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed geometry injects one active source-localization owner fibre into
the complete ambient block of side `ell = L^(depth+1)`.  Its cardinality is
therefore at most `ell^4`, and an arbitrary counting-L2 input supported in
that fibre obeys the exact four-dimensional conversion

```text
norm f <= ell^2 * finitePiLpSupNorm f.
```

No factor depending on the regional parameter `K`, the torus parameter `Q`,
or the ambient volume is introduced.  This is the input-size component of
the first printed CMP99 (3.42) scale `ell^2`; it is not a derivation of the
localized Green action.  In particular it does not produce uniform `B0` or
`delta0`, the left/right derivative and Laplacian estimates, the physical
Eq. (3.89) contraction, rows 23--24, or a `TermSource` inhabitant.  The
existing entrywise Combes--Thomas kernel cannot be summed over the source
fibre without losing the printed scale; the remaining producer must retain
the block-localized source quantifier.

The primary proof chain now localizes the remaining source boundary exactly.
CMP99 Corollary 3.6 gauges each regular cell background into the near-identity
regime and imports the zero-background local Green estimates from CMP96 [4],
Proposition 2.2 / equation (2.67).  Those estimates feed the local `G'_Pi`
used in (3.89); Theorem 3.7 then combines (3.89), CMP96 Lemma 2.1, and the
random-walk formula (3.90) to recover global Theorem 3.1.  Therefore neither
the existing coarse Combes--Thomas reciprocal-coercivity bound nor a new
record that simply assumes the four fields of (2.67) is an admissible next
producer.  The next source-analytic brick must begin below (2.67), at the
CMP96 zero-background localized Green construction, and transport it through
the CMP99 near-identity/gauge dictionary.

Direct visual inspection of the newly recovered CMP89 primary source sharpens
that boundary by one full paper.  CMP95 reduces its local propagator estimates
through (1.132)--(1.137), while CMP96 uses its local zero-background bounds in
(2.43) and Proposition 2.2 / (2.67).  The underlying source theorem is CMP89
Lemma 2.4: (2.35)--(2.37) are proved by the explicit Fourier representation
(2.43)--(2.49), the denominator and summability estimates (2.50)--(2.51), and
a complex contour shift in a strip whose width and bound are uniform in the
scale `j`.  CMP89 Lemma 2.2 then transports those zero-background estimates
through (2.34) and the small regular-background perturbation.  No further
paper is cited for this local analytic step.

Thus the first honest missing producer is now the typed zero-background
Fourier/analytic-strip construction of CMP89 (2.43)--(2.51), followed by the
named CMP89/CMP95/CMP96/CMP99 scaling, averaging, boundary and gauge
dictionaries.  It is not another generic Combes--Thomas theorem and it is not
a record containing the four desired outputs.  This source recovery changes
neither the `20/41` numerator nor window 15: no Lean theorem has yet produced
`B0` and `delta0` uniformly for the literal regional Green.

Diagnostic run `31221320009` retained the first elaboration errors in the
decidable fibre filter and subtype-cardinality conversion.  Replacing the
latter with an explicit injection into the ambient block gave cached
diagnostic run `31221547246`; only the cold run above retired
PRE-VALIDATION.  The live counters remain exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5r real sinc-amplitude lower bound for CMP89 (2.45) (SEALED; complex dictionary open)

Exact source checkpoint `af70e5746a1b0a017a4c2fcb7b915a7837bcc114`
passed cold GitHub Actions run
[`31226045386`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31226045386)
(workflow checkpoint `5db1d41aa0c83dab014aa6ae61987ab3c13ae041`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-07T23:08:01Z` to `23:08:05Z`, exited
zero, and ended with `Build completed successfully (3273 jobs).`; the audit
ended at `23:08:12Z`.  All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed source subbrick defines the real removable sinc quotient beneath
the one-coordinate factor of CMP89 (2.45) and proves

```text
2 / pi <= |sinc(p/2) / sinc(xi*p/2)|
```

for `0 < xi <= 1` and `|p| <= pi`.  Multiplication over `Fin d` gives the
uniform lower bound `(2/pi)^d`, and the literal source specialization
`xi = ((L : R)^j)^(-1)` is proved to lie in `(0,1]` for every nonzero natural
block size.  Thus the elementary positive-amplitude input used by the central
alias term of CMP89 (2.50) is now compiler verified uniformly in the RG scale.

This is not yet the complex source symbol of (2.45).  In particular the seal
does not identify the norm of the exponential quotient with the real sinc
amplitude, compare the two Laplacian symbols, prove the full denominator
bound (2.50), establish the momentum sum (2.51), or construct the uniform
analytic strip and contour displacement.  It produces no physical `B0` or
`delta0`, does not attain window 15, discharges no row 23--24, and does not
inhabit `TermSource`.  The live counters remain exactly `20/41` and zero.

Diagnostic runs `31225389994`, `31225569110`, and `31225726131` preserve the
successive elaboration errors.  Cached run `31225904376` passed; only the cold
run above retired PRE-VALIDATION.  The next honest brick is the exact norm
dictionary from the removable complex exponential quotient in (2.45) to this
real sinc amplitude, before any use in (2.50).

### Step 7.5s exact complex-to-sinc dictionary for CMP89 (2.45) (SEALED; denominator comparison open)

Exact source checkpoint `08acaa13dc8cf79a5d5beb666540b295e158517c`
passed cold GitHub Actions run
[`31227914423`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31227914423)
(workflow checkpoint `813914e4922f1d185b4b77710062484645af6149`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-07T23:43:50Z` to `23:43:56Z`, exited
zero without warnings, and ended with
`Build completed successfully (3274 jobs).`; the audit ended at `23:44:00Z`.
All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick defines the exponential difference slope with its removable
value at zero and forms the CMP89 coordinate factor as the quotient of slopes
at `p` and `xi*p`.  It proves, for all real `xi,p`, the exact identity

```text
norm(complexAverageFactor xi p) =
  |sinc(p/2) / sinc(xi*p/2)|.
```

Away from the `p = 0` and `xi = 0` branches, a separate theorem identifies
that object algebraically with the literal printed quotient
`(exp(-i p)-1) / ((exp(-i xi p)-1)/xi)`.  The product norm is therefore
exactly the real amplitude sealed in Step 7.5r, and its source-specialized
lower bound `(2/pi)^d` is transported to the complex product uniformly in
the RG scale.

This closes the first dictionary explicitly left open by Step 7.5r.  It does
not compare `Delta^xi(p)` with the continuum/lattice momentum symbols, prove
the full alias denominator estimate (2.50), establish the momentum sum
(2.51), or construct the uniform analytic strip.  Hence it produces no
physical `B0` or `delta0`, does not attain window 15, discharges no row
23--24, and does not inhabit `TermSource`.  The live counters remain exactly
`20/41` and zero.

Runs `31226608914`, `31226774446`, and `31226972700` preserve the three
elaboration errors.  Earlier green runs `31227277987` and `31227593499` were
superseded solely to remove linter warnings; cached run `31227769422` and the
cold run above certify the warning-free source.  The next honest producer is
the pair of Laplacian-symbol comparisons used by the central alias term of
(2.50), before summing the noncentral aliases.

### Step 7.5t central Laplacian comparison for CMP89 (2.50) (SEALED; full central alias open)

Exact source checkpoint `1998e2fb71ce126940639cef8fe894642850c430`
passed cold GitHub Actions run
[`31228925432`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31228925432)
(workflow checkpoint `8f344357d5d16fa6fccd0e4fb382ad9b356cbc7c`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T00:03:43Z` to `00:03:51Z`, exited
zero without warnings, and ended with
`Build completed successfully (3275 jobs).`; the audit ended at `00:03:58Z`.
All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick defines the literal coordinate norms and the massive
fine- and unit-lattice Laplacian symbols below (2.50).  Jordan's inequality
and the exact exponential-difference norm give, on the Brillouin box and for
positive `xi`,

```text
Delta^xi(p) <= (pi / 2)^2 * Delta^1(p).
```

For positive mass this is inverted without a `0/0` branch:

```text
((pi / 2)^2)^(-1) <= Delta^1(p) / Delta^xi(p).
```

This supplies the Laplacian-ratio half of the central alias lower bound in
(2.50).  It does not yet multiply that ratio by the sealed complex averaging
amplitude, sum the noncentral aliases, establish (2.51), or construct the
uniform analytic strip.  Hence it produces no physical `B0` or `delta0`,
does not attain window 15, discharges no row 23--24, and does not inhabit
`TermSource`; the live counters remain exactly `20/41` and zero.

Runs `31228493253` and `31228644041` preserve the two elaboration corrections;
cached run `31228790898` passed the final source, and only the cold run above
retired PRE-VALIDATION.  The next honest producer combines this reciprocal
ratio with the Step-7.5s complex-amplitude lower bound to close the central
alias term of (2.50), before any noncentral summation.

### Step 7.5u central alias lower bound for CMP89 (2.50) (SEALED; noncentral aliases open)

Exact source checkpoint `b7de5c4d80af961acdfaba349ba09d8b54d9c591`
passed cold GitHub Actions run
[`31229579111`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31229579111)
(workflow checkpoint `3096c9597395d755fddc8847a40e6cf0a3ba9d99`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T00:17:36Z` to `00:17:47Z`, exited
zero without warnings, and ended with
`Build completed successfully (3276 jobs).`; the audit ended at `00:17:52Z`.
All four audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick retains the positive source coefficient `a` explicitly and
proves the exact equality between the literal source order

```text
a * |u_j(p)|^2 / Delta^xi(p) * Delta^1(p)
```

and its factorized core.  Multiplying the Step-7.5s averaging-amplitude lower
bound with the Step-7.5t reciprocal Laplacian ratio gives the uniform lower
constant

```text
a * ((2 / pi)^d)^2 * ((pi / 2)^2)^(-1),
```

which is separately proved strictly positive for `0 < a`.  Thus the central
alias contribution in (2.50) is now closed without a free family or a hidden
`0/0` convention.

The full denominator estimate (2.50) still needs the exact finite source
alias set, membership of the central alias `l'=0`, and nonnegativity of every
remaining summand.  The printed proof then discards the noncentral terms; it
does not require a quantitative bound on them.  Their decay estimates enter
later in (2.51), which remains open together with the uniform analytic strip
and the Fourier-to-regional-Green dictionary.  Therefore this brick produces
no physical `B0` or `delta0`, does not attain window 15, discharges no row
23--24, and does not inhabit `TermSource`.  The counters remain exactly
`20/41` and zero.

Run `31229284523` preserves the single associativity elaboration correction;
cached run `31229442243` passed the final source, and only the cold run above
retired PRE-VALIDATION.  The next honest Fourier brick is the exact centered
alias enumeration from (2.45), its zero-member theorem, and the resulting
nonnegative-sum completion of (2.50).  Quantitative noncentral estimates are
deferred to (2.51), exactly as in the source.

### Step 7.5v full denominator lower bound CMP89 (2.50) (SEALED; summability (2.51) open)

Exact source checkpoint `b84a28046e249df62e56d1b67f5030308830b90e`
passed cold GitHub Actions run
[`31230322062`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31230322062)
(workflow checkpoint `e8e1397c0b2d6436c53e39f2ff608fc9087cadc3`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T00:32:59Z` to `00:33:13Z`, exited
zero without warnings, and ended with
`Build completed successfully (3277 jobs).`; the audit ended at `00:33:19Z`.
All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed module constructs the centered coordinate representatives printed
in (2.45): a closed interval for odd alias count and the half-open interval
for even alias count.  Their `d`-fold product contains the all-zero alias for
every nonzero block size, including the coherent singleton at `j=0`.  The
literal shifts are `l'_mu = 2*pi*m'_mu`.

Every denominator summand is nonnegative under positive mass.  The complete
finite denominator from (2.50) therefore dominates its zero-alias summand,
and the Step-7.5u constant gives the literal full estimate

```text
a * ((2 / pi)^d)^2 * ((pi / 2)^2)^(-1)
  <= a * (sum over l' of |u_j(p+l')|^2 / Delta^xi(p+l'))
       * Delta^1(p) + Delta^1(p).
```

This closes (2.50) without importing any noncentral decay hypothesis.  The
quantitative estimate over `l != 0` in (2.51), the uniform analytic strip,
and the Fourier-to-regional-Green dictionary remain open.  Thus no physical
`B0` or `delta0` is produced yet, window 15 remains unattained, no row
23--24 is discharged, and `TermSource` remains uninhabited; the counters stay
exactly `20/41` and zero.

Run `31230025181` preserves the sole product-association elaboration repair;
cached run `31230196579` passed the final source, and only the cold run above
retired PRE-VALIDATION.  The next source brick is the explicit polynomial
alias summability in (2.51), keeping the later complex-strip argument as a
separate frontier.

### Step 7.5w one-dimensional alias series for CMP89 (2.51) (SEALED; d-fold factorization open)

Exact source checkpoint `c0bfd4f0be0dc9c28ed4d3b6237b255e38f97e9f`
passed cold GitHub Actions run
[`31231324004`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31231324004)
(workflow checkpoint `98b1ee69b033c4e3ffd89a18ffdf3ec598693a09`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T00:55:42Z` to `00:55:59Z`, exited
zero without warnings, and ended with
`Build completed successfully (3281 jobs).`; the audit ended at `00:56:05Z`.
All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick defines the literal source exponent

```text
s(d, alpha) = 1 + (1 - alpha) / d
```

and proves `1 < s(d, alpha)` for positive dimension and `alpha < 1`.  Its
coordinate weight is exactly

```text
1 / (1 + |2*pi*m|)^s,   m in Z.
```

The central alias is separated explicitly.  Every noncentral term is bounded
by the standard integer p-series `|m|^(-s)`, which proves summability on all
of `Z`.  Consequently every finite centered coordinate window from (2.45),
for every alias count `N`, is bounded by one and the same infinite-series
constant.  No cardinality factor depending on `L^j` is introduced.

This does not yet factor the `d`-dimensional sum over `Fintype.piFinset`,
prove the complete integrand comparison in (2.51), or construct the uniform
complex strip used after (2.51).  Hence it produces no physical `B0` or
`delta0`, does not attain window 15, discharges no row 23--24, and does not
inhabit `TermSource`; the live counters remain exactly `20/41` and zero.

Runs `31230761932`, `31230900496`, and `31231081213` preserve the three local
elaboration repairs.  Cached run `31231215536` passed the final source, and
only the cold run above retired PRE-VALIDATION.  The next honest brick is the
exact finite-product identity supplied by `Finset.sum_prod_piFinset`, followed
only then by the coordinatewise bound.  The physical integrand and analytic
strip remain later frontiers.

### Step 7.5x multidimensional alias product for CMP89 (2.51) (SEALED; physical integrand open)

Exact source checkpoint `1722033a62ab84ed2f545e42f0a0aa1a81784809`
passed cold GitHub Actions run
[`31231854020`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31231854020)
(workflow checkpoint `878e871ae9640c88945f6f77d6ba7da1ecbad8fc`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T01:08:16Z` to `01:08:35Z`, exited
zero without warnings, and ended with
`Build completed successfully (3282 jobs).`; the audit ended at `01:08:39Z`.
All four audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick defines the literal product of the Step-7.5w coordinate
weights over `Fin d` and proves the exact finite identity

```text
sum_(m in S^d) product_mu w(m_mu) = (sum_(n in S) w(n))^d
```

for the centered source alias set `S` of (2.45).  The proof uses
`Finset.sum_prod_piFinset`; it does not estimate the size of `S`.  Monotonicity
of nonnegative powers then transports the sealed coordinate-series estimate
to a bound by the `d`-th power of one scale-independent infinite series.

This is the last algebraic factorization in the displayed derivation (2.51),
but it is not yet the complete estimate: the physical Fourier summand still
has to be bounded by this product weight using the source estimates preceding
the last line of (2.51).  The uniform complex strip and contour displacement
also remain separate.  Thus no physical `B0` or `delta0` is produced, window
15 remains unattained, no row 23--24 is discharged, and `TermSource` remains
uninhabited; the live counters stay exactly `20/41` and zero.

Run `31231616924` preserves the sole under-binder unfolding repair; cached run
`31231751244` passed the final source, and only the cold run above retired
PRE-VALIDATION.  The next honest brick is the literal physical-summand
comparison in the first two inequalities of (2.51), with its Laplacian ratio,
one distinguished momentum coordinate and the noncentral `|p+l|` decay kept
visible.

### Step 7.5y expanded source-alias geometry for CMP89 (2.45)--(2.51) (SEALED; expanded symbol bounds open)

Exact source checkpoint `336fdf35348ebd4e521a9f400a3284429e9d31b0`
passed cold GitHub Actions run
[`31232745194`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31232745194)
(workflow checkpoint `1869742e9fb83b7cd99f3d5d07bc4c2f8fa0a356`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T01:30:59Z` to `01:31:18Z`, exited
zero without warnings, and ended with
`Build completed successfully (3283 jobs).`; the audit ended at `01:31:22Z`.
All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The printed even representative set in (2.45) is not pointwise contained in
the central scaled Brillouin interval.  The sealed counterexample is literal:
for alias count `N=2`, momentum `p'=-pi` and centered alias `m=-1`,

```text
|N^-1 * (p' + 2*pi*m)| = 3*pi/2 > pi.
```

Thus the central-alias Jordan lemma cannot be reused silently for every
noncentral term in (2.51).  The same module proves the positive replacement:
membership in the exact centered source set implies `2*|m| <= N`, hence
`|p'+2*pi*m| <= pi*(N+1)` and, for every positive `N`, the uniform scaled
radius `|N^-1*(p'+2*pi*m)| <= 3*pi/2`.

This is a dictionary correction, not the physical integrand estimate.  The
next finite source-facing chain is now explicit: an expanded-zone lower bound
for the lattice difference/sinc denominator; the averaging-amplitude upper
bound; the noncentral Laplacian-ratio upper bound; the Holder exponential
difference; and only then the complete comparison with the already sealed
coordinate-product weight.  The analytic strip remains later and separate.
No physical `B0` or `delta0` is produced, window 15 remains unattained, no
row 23--24 is discharged, and the live counters stay exactly `20/41` and
`TermSource = 0`.

Run `31232268327` was stopped by the ten-key cache preflight before Lean.
Run `31232327344` preserves the two local elaboration repairs; cached run
`31232461649` passed.  Cold run `31232600125` was mathematically green but
retained PRE-VALIDATION because of one linter warning.  Only the warning-free
cold run above retired it.

### Step 7.5z expanded difference and sinc lower bounds for CMP89 (2.51) (SEALED; amplitude numerator open)

Exact source checkpoint `4bf1f1bec890d1dbcf34a0d958ae10b9251e0146`
passed cold GitHub Actions run
[`31233308717`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31233308717)
(workflow checkpoint `ae0740f7563d9feac34f4bcb7b6e8a1b338d3b64`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T01:45:00Z` to `01:45:29Z`, exited
zero without warnings, and ended with
`Build completed successfully (3284 jobs).`; the audit ended at `01:45:37Z`.
All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed brick proves the explicit expanded-zone Jordan estimate

```text
(1/(3*pi))*|x| <= 2*|sin(x/2)|,    |x| <= 3*pi/2,
```

then transports it to the literal unit and scaled lattice-difference symbols
of (2.45).  It also proves `1/(3*pi) <= |sinc(x/2)|` on the same zone.  Using
Step 7.5y's exact alias radius specializes both conclusions to every member of
the printed centered representative set, including the even extreme that lies
outside `[-pi,pi]`.  No central-alias theorem is silently reused.

This closes the denominator-side obstruction exposed by the no-go, but not
the numerator-side averaging decay.  The remaining real chain to the first
inequalities of (2.51) is: periodic numerator/sinc amplitude upper bound;
noncentral Laplacian-ratio upper bound with the physical mass range visible;
Holder exponential difference; and final comparison with the sealed product
weight.  The complex strip remains later and separate.  No physical `B0` or
`delta0` is produced, window 15 remains unattained, no row 23--24 is
discharged, and the live counters stay exactly `20/41` and `TermSource = 0`.

Run `31233039423` preserves the sole complex-cast dictionary repair; cached
run `31233192928` passed the final source, and only the cold run above retired
PRE-VALIDATION.

### Step 7.5aa periodic alias-amplitude upper bound for CMP89 (2.51) (SEALED; Laplacian ratio open)

Exact source checkpoint `b7ba6f63c066603f2f8c8dc39301801cba4cf09c`
passed cold GitHub Actions run
[`31233987197`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31233987197)
(workflow checkpoint `82d8beab77da54310a3bb351296984ec8c078ade`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T02:02:46Z` to `02:03:14Z`, exited
zero without warnings, and ended with
`Build completed successfully (3285 jobs).`; the audit ended at `02:03:20Z`.
All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed producer proves the literal reciprocal-lattice periodicity
`|sin((p+2*pi*m)/2)| = |sin(p/2)|` and the noncentral separation
`pi*|m| <= |p+2*pi*m|` for `|p| <= pi`.  Consequently the removable numerator
sinc is at most `6` times the exact source weight
`(1+|2*pi*m|)^(-1)`.  Combining this with Step 7.5z leaves the denominator
cost visible and gives the coordinate estimate

```text
|u_j(p+2*pi*m)| <= 18*pi/(1+|2*pi*m|).
```

Finite-product multiplication yields both the real and complex
`d`-dimensional amplitude bounds by `(18*pi)^d` times the sealed
multidimensional alias weight.  Every printed odd/even alias is covered and
no alias cardinality is introduced.

This closes only the averaging-amplitude numerator.  The noncentral
Laplacian-ratio upper bound with the physical mass range visible, the Holder
exponential difference, the complete comparison in (2.51), and the uniform
analytic strip remain open.  No physical `B0` or `delta0` is produced, window
15 remains unattained, no row 23--24 is discharged, and the live counters
stay exactly `20/41` and `TermSource = 0`.

Run `31233738503` preserves the sole exponent-normalization elaboration
failure.  Cached run `31233870292` passed the repaired source, and only the
cold run above retired PRE-VALIDATION.

### Step 7.5ab noncentral massive-symbol ratio for CMP89 (2.51) (SEALED; mass-flow dictionary open)

Exact source checkpoint `492318060dbf3b2ab9483f413151665df59ed39c`
passed cold GitHub Actions run
[`31234910793`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31234910793)
(workflow checkpoint `519f3651f0635a38eba91b5a01f06a2c226f8c7b`).  The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped.  The focal ran from `2026-08-08T02:26:51Z` to `02:27:26Z`, exited
zero without warnings, and ended with
`Build completed successfully (3286 jobs).`; the audit ended at `02:27:33Z`.
All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed producer proves the literal massive-symbol comparison

```text
Delta^1(p) / Delta^(1/N)(p+2*pi*m)
  <= (3*pi)^2 (d*pi^2 + 1) / |p+2*pi*m|^2
```

for every nonzero printed alias, under the explicit condition `mass^2 <= 1`.
The lower scaled-symbol estimate uses the already sealed expanded alias zone
and keeps the coarse constant `1/(3*pi)` visible.  The theorem is not uniform
over arbitrary mass and does not claim that the RG family satisfies the mass
condition.

Primary visual review of CMP89 printed pp. 584--586 confirms that (2.44)--(2.51)
use the scale-indexed quantity `m_j^2`, while the action displayed at the start
of Section 3 uses `m_k^2`.  The law relating these masses across scales is not
printed on those pages.  Primary cross-source evidence nevertheless fixes the
direction and dimensional dictionary.  CMP97 printed p. 300 writes the
unit-lattice mass coefficient as `(m^2 + delta m^2) * epsilon^2`; CMP114 printed
p. 273 says that after `n` RG transformations the unit lattice represents
spacing `L^n * epsilon`.  Thus the dimensionless mass at that stage is
`m_phys * L^n * epsilon`.  In CMP89's reverse index, `epsilon = L^(-k)` and
`n = k-j`, so the candidate source dictionary is

```text
m_j = L^(k-j) * m_k = m_phys * L^(-j).
```

The mass therefore grows along forward coarse graining (`n` increases, `j`
decreases), but only up to the unit-scale physical mass.  Uniform
`m_j^2 <= 1` for `0 <= j <= k` follows from the physical normalization
`m_phys^2 <= 1`, equivalently the fine-lattice restriction
`m_k^2 <= L^(-2*k)`.  It is **not** a sixteenth freely chosen smallness window
and it is not a depth-independent choice of the bare dimensionless mass.  The
exact normalization and index convention must still be checked directly in
CMP85 Eq. (2.43), which CMP89 cites for the RG decomposition; until that check
and the Lean dictionary are installed, the brick remains conditional.

The Holder exponential difference, complete real integrand comparison in
(2.51), uniform analytic strip and transport remain open.  No physical `B0` or
`delta0` is produced, window 15 remains unattained, no row 23--24 is
discharged, and the live counters stay exactly `20/41` and `TermSource = 0`.

Cached diagnostic run `31234809751` passed the final source.  Only the cold run
above retired PRE-VALIDATION.

### Step 7.5ac Euclidean Holder phase quotient for CMP89 (2.49)--(2.51) (SEALED; real integrand comparison open)

Exact source checkpoint `52ca4c60f2269e322d00531ec89bd7dabbdbb91e`
passed cold GitHub Actions run
[`31236522003`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31236522003)
(workflow checkpoint `adc9893a58e46f63ead8ec0eff87cbb5c39e46dd`). The run
recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. The focal ran from `2026-08-08T03:09:44Z` to `03:10:10Z`, the audit
ended at `03:10:13Z`, both exited zero without warnings, and the build closed
with `Build completed successfully (3287 jobs).` All five audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`. The
deterministic evidence archive has SHA-256
`9ad16f4b1a633c72c162937e1cc3a3ec78bfcfba1f39dc13a53d96ce5e9838cc`,
reproduced by the local downloaded artifact.

The sealed producer uses the literal source Euclidean norm

```text
|q|_2 = sqrt (sum_mu q_mu^2)
```

and proves the Cauchy--Schwarz phase estimate together with the global scalar
bound `|exp(i*t)-1| <= 2*|t|^alpha` for `0 <= alpha <= 1`. Consequently, for
nonzero displacement `r`, it obtains the exact source-shaped quotient

```text
|exp(i*q.r)-1| / |r|_2^alpha <= 2*|q|_2^alpha.
```

No sup-norm replacement, hidden dimension factor or small-phase hypothesis is
used. This closes only the Holder exponential-difference factor printed on
CMP89 p. 585. The next source-specific frontier is the complete real
integrand comparison in (2.51), in particular the explicit distribution of
the residual `|p+l|^(alpha-1)` factor over the product alias weights. The
uniform analytic strip and transport remain open. No physical `B0` or
`delta0` is produced, window 15 remains unattained, no row 23--24 is
discharged, and the live counters remain exactly `20/41` and
`TermSource = 0`.

Diagnostic run `31236295605` preserved the sole finite-sum elaboration error.
Cached run `31236414962` passed the repaired source; only the cold run above
retired PRE-VALIDATION.

### Step 7.5ad noncentral alias-weight redistribution for CMP89 (2.51) (SEALED; physical integrand assembly open)

Exact source checkpoint `351270d9465fe5c9fd934753ae73044cdd6c6b03`
passed cold GitHub Actions run
[`31237236126`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31237236126)
(workflow checkpoint `e58aa11b3531ebecf5c9d5c1b5f5e3f1029e0894`). The run
recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. The focal ran from `2026-08-08T03:29:31Z` to `03:30:11Z`, the audit
ended at `03:30:15Z`, both exited zero without warnings, and the build closed
with `Build completed successfully (3288 jobs).` All five audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`51c35d0606cbddafebec77aad263c5d61d572f5553353782cc92f4b62dcd5258`,
reproduced after downloading artifact `9015859150`; GitHub reports artifact
digest `ba3dea8636a7fe09fdef51dff336385abcb5f43f491095012e6ab3be7f4f0ef3`.

For every nonzero reciprocal alias `m`, central momentum `p`, positive
dimension and `alpha <= 1`, the sealed producer proves the literal source
redistribution

```text
|p+2*pi*m|_2^(alpha-1)
  * product_mu (1+|2*pi*m_mu|)^(-1)
<= 3^(1-alpha)
  * product_mu (1+|2*pi*m_mu|)^(-(1+(1-alpha)/d)).
```

The proof first establishes the coordinate estimate
`1+|2*pi*m_mu| <= 3*|p+2*pi*m|_2` and then splits the excess exponent uniformly
over the `d` coordinates. No `max` norm, hidden dimension factor or alias
cardinality enters. The central alias is intentionally excluded: it is the
separate `O(1)` term in the printed (2.51).

This closes the residual noncentral geometry, not the complete physical
integrand. The next brick must assemble the scaled derivative factor,
averaging amplitude, massive-symbol ratio, Holder quotient and this
redistribution, with an explicit central/noncentral split. The uniform
analytic strip and physical transport remain open. No physical `B0` or
`delta0` is produced, window 15 remains unattained, no row 23--24 is
discharged, and the counters remain exactly `20/41` and `TermSource = 0`.

Cached diagnostic run `31237103246` passed but retained PRE-VALIDATION. Only
the cold run above retired it.

### Step 7.5ae literal noncentral real integrand in CMP89 (2.51) (SEALED; central branch and alias sum open)

Exact source checkpoint `83272ce580198092dcc516c34e2a353a1bee42b8`
passed cold GitHub Actions run
[`31238106632`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31238106632)
(workflow checkpoint `eb27ce65d6b3c451da33821c5bdcfdb889f53277`). The run
recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. The focal ran from `2026-08-08T03:52:34Z` to `03:53:17Z`, the audit
ended at `03:53:22Z`, both exited zero without warnings, and the build closed
with `Build completed successfully (3289 jobs).` All four audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`aafc1f28c7ebf52d297aaa7f9f07ad19605c366d2eddfff61bf4e6d4ac6e1f8b`,
reproduced after downloading artifact `9016145344`; GitHub reports artifact
digest `16bc3f2611f711d74b34b82cc20a9f3ded6633e19a1f1d1f006c3c03f11fd021`.

For every nonzero printed alias, the sealed endpoint constructs the literal
product of the Holder phase quotient, the inverse complete denominator, one
scaled derivative, the complex averaging amplitude and the massive-symbol
ratio. It proves that product is bounded by the exact summable coordinate
weight with exponent `1+(1-alpha)/d`, paying the fully visible constant

```text
2 * centralLower(d,a)^(-1) * (18*pi)^d
  * ((3*pi)^2 * (d*pi^2+1)) * 3^(1-alpha).
```

No free bound replaces a source factor, and no alias cardinality or hidden
dimension constant enters. The condition `mass^2 <= 1` remains the named
flowing-mass hypothesis already classified in the source map; this theorem
does not assert that RG dynamics preserves it. The central alias, finite alias
sum, uniform analytic strip and physical Green transport remain open. This is
infrastructure below window 15, not a terminal field: counters remain exactly
`20/41`, `TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5af central `O(1)` real integrand in CMP89 (2.51) (SEALED; finite alias sum open)

Exact source checkpoint `f39ad20aa11e47db37bc12bd6c612d7b5b844e26`
passed cold GitHub Actions run
[`31238966942`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31238966942)
(workflow checkpoint `9fbaeb9670eb55b640c4dc29699d2ce59ad8bf9f`). The run
recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. The focal ran from `2026-08-08T04:15:40Z` to `04:16:18Z`, the audit
ended at `04:16:24Z`, both exited zero without warnings, and the build closed
with `Build completed successfully (3290 jobs).` All eight audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`7ee7d554d3f72659719c9e1720f7859c301e7f0eea3b5a400d9a7ae299f5f2d9`,
reproduced after downloading artifact `9016401875`; GitHub reports artifact
digest `f30183f173cac75b085a38021195007afb3dd40156e8d7fa7087b0099d4d4fec`.

The sealed endpoint handles the zero alias separately, exactly as the source
does. The central Brillouin cube has explicit Euclidean radius
`sqrt(d*pi^2)`; the Holder and derivative factors are uniformly controlled on
that cube, the amplitude contributes `(18*pi)^d`, and the same-momentum massive
symbol quotient is at most `(3*pi)^2`. Consequently the central branch has an
explicit `O(1)` bound and does not require `mass^2 <= 1`; that flowing-mass
condition belongs only to the noncentral inverse-square estimate.

The remaining real-variable step in (2.51) is the exact finite alias split and
sum, using this central constant once and the noncentral product series for all
other aliases. The uniform analytic strip and physical Green transport remain
open. This is infrastructure below window 15, not a terminal field: counters
remain exactly `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.


Runs `31238460271`, `31238613347` and `31238736048` preserve the three
elaboration failures. Cached diagnostic run `31238863986` passed but retained
PRE-VALIDATION; only the cold run above retired it.

### Step 7.5ag exact finite real-integrand alias sum in CMP89 (2.51) (SEALED; analytic strip open)

Exact source checkpoint `c1b7aa941688a8e3e7003f3b3a9142cc8db9dccd`
passed cold GitHub Actions run
[`31239705795`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31239705795)
(workflow checkpoint `67247bb7b8f83d280dc74ff13741c8d38153c43c`). The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped. The focal ran from `2026-08-08T04:35:02Z` to `04:35:51Z`, the audit
ended at `04:35:55Z`, both exited zero without warnings, and the build closed
with `Build completed successfully (3291 jobs).` All three audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`90ce34305c9b5cc50e7ad9e0f6f5008ea527d415a7566dd128d943ffbf7d9b14`,
reproduced after downloading artifact `9016637971`; GitHub reports artifact
digest `b527775ba33fe24c36e0c06275e47a198b03cc560af5890b5a81d79ef6546214`.

The sealed endpoint splits the exact finite reciprocal-alias set with
`Finset.sum_erase_add`: the zero alias contributes the central constant once,
and every remaining alias is bounded by the noncentral product weight. The
finite product sum is then dominated by the already sealed infinite
one-dimensional series raised to the `d`-th power. No alias cardinality enters.
The condition `mass^2 <= 1` is consumed only by the noncentral branch; it is
not imposed on the central `O(1)` term and is not reclassified as a selectable
smallness window.

The uniform complex analytic strip, Fourier contour shift and transport to the
physical regional Green remain open. This is infrastructure below window 15,
not a terminal field: counters remain exactly `20/41`, `TermSource = 0`, and
window 15 compatible but unattained. Runs `31239333700` and `31239462882`
preserve the two elaboration failures; cached run `31239604206` was diagnostic
only and did not retire PRE-VALIDATION.

### Step 7.5ah entire finite averaging amplitude and printed-alias real slice (SEALED; complex denominator open)

Exact source checkpoint `a414b2370c78230856905843cdf327cb56fc4eba`
passed cold GitHub Actions run
[`31241734442`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31241734442)
(workflow checkpoint `2d268b58e944b0bd62f72a5965fc45fe47b456f5`). The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped. Dependency materialization ended at `05:29:49Z`; the focal ended at
`05:30:25Z`, and the three audits ended at `05:30:30Z`, `05:30:34Z` and
`05:30:39Z`. All four stages exited zero without focal warnings, and the build
closed with `Build completed successfully (3288 jobs).` The six generic,
one slope-nonvanishing and two physical-dictionary declarations all use
exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`62c7d2a6e98b8d1b54eb217dcecd1aaa61efa7154c85c8e1ec6b365f3fe9a74d`,
reproduced after downloading artifact `9017266698`; GitHub reports artifact
digest `24dcc599de11b14265d68d0519cec4db05ed7d80317ece166b31efdec80e13fd`.

The sealed producer replaces the removable exponential quotient in CMP89
(2.45) by its finite geometric sum at inverse integer scale. The resulting
one-coordinate factor and its finite-coordinate product are entire, and the
printed expanded-zone lower bound proves the denominator slope is nonzero on
every real alias. Consequently the entire product agrees exactly with the
already sealed physical averaging amplitude on that real slice.

This does not yet construct the holomorphic massive denominator. That object
must use the analytic pairing `u(z) * u(-z)` rather than a complexified norm
square. Its uniform nonvanishing strip, the Fourier contour shift and transport
to the physical regional Green remain open. The flowing condition
`mass^2 <= 1` is unchanged and remains a physical RG-scaling obligation, not a
sixteenth selectable window. This is infrastructure below window 15, not a
terminal field: counters remain exactly `20/41`, `TermSource = 0`, and window
15 compatible but unattained. Runs `31240261083`, `31240392858`,
`31240518802`, `31240663340`, `31240791368`, `31240943095`, `31241218628`,
`31241360285` and `31241511690` preserve the elaboration failures. Cached run
`31241632503` passed but retained PRE-VALIDATION; only the cold run above
retired it.

### Step 7.5ai entire lattice-difference, Laplacian and averaging pairings (SEALED; uniform strip open)

Exact source checkpoint `47a5cb3b626426104ae0f7ef4afd98a2b3aea372`
passed cold GitHub Actions run
[`31242779236`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31242779236)
(workflow checkpoint `0e6879cb1cdf93eb924a3aa6e68d5098208a0986`). The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped. The focal ran from `05:57:48Z` to `05:58:02Z`, the audit ended at
`05:58:09Z`, both exited zero without focal warnings, and the build closed with
`Build completed successfully (3277 jobs).` All eleven audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`1cfe4df0f678995b4acdf13bf1d3c699659c26cc26a12c98deb7006f291b081e`,
reproduced after downloading artifact `9017562424`; GitHub reports artifact
digest `21d5301d6d8de1ccf6c6239a9f51ca710dd7e6f80bd1fa24e905bd2e258144c7`.

The sealed module constructs the entire fine-lattice difference and its
bilinear opposite-momentum Laplacian, together with the corresponding
opposite-momentum pairing of the finite averaging amplitude. On real momentum,
reversal is proved to be complex conjugation; hence the two pairings recover
exactly the nonnegative scaled Laplacian and the squared averaging norm used in
CMP89 (2.47)--(2.49). This is the analytic continuation of the source factors,
not a complexification of their norm squares.

No inverse is taken. Uniform nonvanishing of the complete complex denominator,
the analytic strip, contour displacement and regional-Green transport remain
open. The condition `mass^2 <= 1` is absent from this construction and remains
a flowing physical-mass obligation, not a sixteenth selectable window. This is
infrastructure below window 15: counters remain exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained. Run `31242420869`
preserves the failed automatic `fun_prop` composition; cached run `31242614452`
passed but retained PRE-VALIDATION. Only the cold run above retired it.

### Step 7.5aj literal complex alias denominator and real-slice dictionary (SEALED; uniform strip open)

Exact source checkpoint `3746b6a4ef58ec387ac6939ee819d99ed7729f07`
passed cold GitHub Actions run
[`31244335533`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31244335533)
(workflow checkpoint `0088e233894cc6ab7c8098877ae27c8f77d8e09f`). The run
recorded `COLD_MODE=true`; restoration and saving of `.lake/build` were both
skipped. The focal ran from `06:39:24Z` to `06:39:53Z`, the audit ended at
`06:39:59Z`, and both exited zero. All nine audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`51d383fb311362cfc65b26637c4c49e9af64f5a749f794cff20398408866882f`;
the downloaded artifact and every entry of `SHA256SUMS` reproduced locally.
GitHub artifact `9018032031` has digest
`eb8af486d0d0ad5399a3eb7c3be8d9107c0e6210a6a9dc3a60772d3927cd16ee`.

The sealed module assembles the literal finite complex denominator of CMP89
(2.47), using the opposite-momentum pairing `u(z+l) * u(-z-l)`, and the full
denominator of (2.49) after multiplication by the entire unit-lattice symbol.
On the printed real alias set, every complex summand and the complete full
denominator agree exactly with the previously sealed real objects.

This does not prove that each fine-lattice quotient is individually pole-free,
nor that the combined expression is nonzero on a scale-uniform strip. The
source asserts analyticity of the complete integrand; removable cancellations
may therefore have to be proved after assembly rather than by excluding every
individual denominator zero. An explicit strip radius, its joint bound
`B0(delta0)`, contour displacement, reflections and physical regional-Green
transport remain open. This is infrastructure below window 15: counters remain
exactly `20/41`, `TermSource = 0`, and window 15 compatible but unattained.
Runs `31243687034`, `31243835860`, `31243976939` and `31244104328` preserve
the four elaboration failures; cached run `31244234625` passed but retained
PRE-VALIDATION. Only the cold run above retired it.

Primary render audit of CMP89 printed pp. 584--586 identifies the quantitative
source of the remaining strip. The full-lattice operator in (2.44) is

```text
-Delta^xi + m_j^2 + a_j Q_j^* Q_j.
```

The positive denominator estimate (2.50) retains the central alias from the
`a_j Q_j^* Q_j` term and proves

```text
a_j * |u_j(p)|^2 * Delta^1(p) / Delta^xi(p) >= O(1) > 0.
```

Thus the printed scale-uniform gap is supplied by the block-averaging penalty,
not by the running mass and not by the free boundary. The boundary reduction
in (2.42) uses multiple reflections only after the full-lattice decay has been
proved. Immediately after (2.51), the source says that the integrand extends
to a neighbourhood of `[-pi,pi]^d` whose width and bound can be chosen
independently of `j`; shifting inside that neighbourhood produces the displayed
factor `exp(-delta0 * distance)`.

Consequently the uniform analytic-strip proof is the common producer of the
zero-background `B0` and `delta0` inputs later consumed by CMP99 (3.42), though
`delta0` is a chosen shift inside the available strip, not definitionally its
maximal radius. The paper prints neither radius nor bound. They must be
constructed from the complete holomorphic denominator and then transported
through reflections and the later scale/gauge dictionaries. In particular,
the heuristic `delta0 ~ mass`, `B0 ~ mass^-2`, and hence `K ~ mass^-7` does not
describe this CMP89 mechanism and must not be used as a gate.

The remaining flow question for the coefficient `a_j` is now resolved against
the primary CMP85 paper. Printed p. 609, Eq. (2.13), defines

```text
a_(k+1) = a*a_k / (a*L^(-2) + a_k),    a_1 = a,
```

and Eq. (2.15) gives the closed form and limit

```text
a_k = a*(1-L^(-2))/(1-L^(-2k))
    decreases to a_infinity = a*(1-L^(-2)).
```

Thus `a>0` and `L>1` imply the scale-uniform floor
`a_k >= a*(1-L^(-2)) > 0`. Printed p. 612, Eq. (2.43), uses the same `a_j^2`
inside the solved propagator decomposition. In dimension four, inserting this
floor into the already sealed real central-alias estimate gives the explicit
uniform real denominator gap

```text
a*(1-L^(-2)) * (2/pi)^10,
```

where `(2/pi)^10 = 0.010934...`. This closes the question whether `a_j`
decays along the source flow. It does **not** yet produce a complex strip or
`B0`: one still has to control the assembled complex denominator/integrand
uniformly near the real cube, including any removable alias cancellations.

### Step 7.5ak CMP85 coefficient floor into the CMP89 real denominator (SEALED; complex strip open)

Exact source checkpoint `e0aaffdc9afc669bcef22aa040768beaf1b88df8`
passed cold GitHub Actions run
[`31245326067`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31245326067)
(workflow checkpoint `8f68f8994a6c91605052f355287001cb0866772e`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal completed 8,407 jobs, focal and audit exited zero, and all five audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The module does not duplicate the source recurrence: it consumes
`cmp99SourceMassParameter`, proves the printed CMP85 (2.15) floor

```text
a * (1 - L^(-2)) <= a_j
```

for every depth, proves the floor strictly positive for `a > 0`, `L > 1`, and
installs it in the complete real CMP89 denominator. Hence in dimension four
the real gap `a * (1 - L^(-2)) * (2/pi)^10` is now a compiled consequence
rather than a source-only calculation.

This closes only the flow-uniformity of the real coefficient. The assembled
complex denominator still needs a `j`-uniform variation bound. The intended
next endpoint is a bound `C` on that complete variation, summed with the same
alias weight as (2.51), followed by a derived radius such as `c_*/(2*C)` and
a joint `B0(delta0)`. Per-scale continuity and independent per-alias
nonvanishing are not accepted substitutes. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5al entire alias-fibre precision matrix (SEALED; stabilized strip open)

Exact source checkpoint `3bd8e2e15f69643c999041b7a18871b3ede086eb`
passed cold GitHub Actions run
[`31247059031`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31247059031)
(workflow checkpoint `8579831b063ce8f71325d650ca29ae5e5f565f56`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal completed 3,291 jobs, focal and audit exited zero, and all four audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

At fixed coarse complex momentum the new module constructs the source system
from CMP89 (2.44)--(2.46) on the finite reciprocal-alias fibre:

```text
diag(Delta_l) + a * u_l * u_{-m}.
```

Its exact action is the diagonal fine symbol plus one rank-one averaging
readout; every matrix entry is entire. On the real slice the row factor is
proved to be the complex conjugate of the column factor and the diagonal is
identified with the literal nonnegative source symbol. This is the correct
home for the cancellations hidden by the solved rational formula (2.46): an
individual displayed `Delta_l` may vanish in complex momentum without making
the assembled matrix expression singular.

The next source-specific endpoint is the exact zero-alias stabilization,
followed by a real lower bound and a scale-uniform complex variation estimate
for that stabilized object. No matrix inverse, strip radius, `B0`, contour
shift or regional-Green transport is claimed here. This is infrastructure
below window 15: counters remain `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

### Step 7.5am central-alias stabilization (SEALED; real gap and strip open)

Exact source checkpoint `d44a4877468fb7f3da595d146ad9529ff77c9d1f`
passed cold GitHub Actions run
[`31247671591`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31247671591)
(workflow checkpoint `eb71e70518b91938a25198ce0529f3256637110e`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal completed 3,292 jobs, focal and audit exited zero, and all three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The solved formula (2.47) is split over the literal zero reciprocal alias and
its complement. The new stabilized denominator is

```text
Delta_0 + a*u_0*u_{-0}
  + a*Delta_0*sum_{l != 0} u_l*u_{-l}/Delta_l,
```

and is proved exactly equal to `Delta_0` times the reduced rational
denominator wherever the original central quotient is defined. Unlike a
product over every alias, this cancellation does not introduce an
`L^(j*d)`-sized degree or constant. It removes the only pole that can approach
the real cube with the running mass; the noncentral denominators remain
visible for their separate geometric strip estimate.

The next endpoint is the real lower bound supplied by `a*u_0*u_{-0}` plus
nonnegative noncentral contributions, followed by a uniform complex variation
bound for this exact stabilized object. No strip radius, `B0`, contour shift
or regional-Green transport is claimed here. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5an stabilized real denominator floor (SEALED; complex variation open)

Exact source checkpoint `798e941733bcd934bbab683923452b941f3fb1ea`
passed cold GitHub Actions run
[`31248239837`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31248239837)
(workflow checkpoint `4755cb07963706c88dc47de506a26e24e3154e0d`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal completed 8,420 jobs, focal and audit exited zero, and all eight audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

On the real momentum cube the stabilized expression is identified exactly
with

```text
Delta_0 + a*|u_0|^2 + a*Delta_0*sum_{l != 0} |u_l|^2/Delta_l.
```

The noncentral sum is nonnegative for positive running mass, so retaining the
central averaging term gives the stronger scale-uniform floor

```text
a_j * (2/pi)^(2d).
```

CMP85 (2.15) is then consumed internally to replace the flowing coefficient
by `a*(1-L^(-2))`. In dimension four the resulting explicit floor is
`a*(1-L^(-2))*(2/pi)^8`; unlike the earlier multiplied (2.50) floor, it does
not pay the extra unit/fine Laplacian comparison factor. The theorem assumes
positive running mass only to reuse nonnegativity of the noncentral rational
summands; the lower constant itself is mass independent.

The remaining endpoint is a scale-uniform complex variation estimate for this
same stabilized object. It must keep the central cancellation assembled and
sum only the geometrically separated noncentral aliases; an alias-cardinality
factor or independent central-denominator nonvanishing is not accepted. No
strip radius, joint `B0`, contour shift or regional-Green transport is claimed.
This is infrastructure below window 15: counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5ao noncentral real gap at zero mass (SEALED; complex strip open)

Exact source checkpoint `5ad7d83a3398438d1ec992167127843b439c587a`
passed cold GitHub Actions run
[`31249442951`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31249442951)
(workflow checkpoint `552c928e82f26bee318e83fdd9c611a682af0a3e`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal completed 8,425 jobs, focal and audit exited zero, and all seven audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

For every printed alias `m != 0`, the already sealed geometry gives
`|p+2*pi*m|_2 >= pi`. The expanded-zone difference lower bound therefore
implies the explicit scale- and mass-independent fine-symbol gap

```text
1/9 <= Delta_m.
```

Hence all noncentral rational summands are nonnegative even at zero mass. The
stabilized real lower bound and its CMP85 coefficient-floor specialization no
longer require `mass > 0`; the uniform real floor is genuinely compatible
with the massless gauge limit. This does not discharge the distinct flowing
window `mass^2 <= 1` used in the upper estimate of the noncentral ratio in
(2.51).

The next complex-strip estimate must use the literal normalization already
present in the entire average,

```text
u_N(z) = N^(-1) * sum_{r < N} exp(-i*(r/N)*z).
```

Thus its frequencies satisfy `r/N < 1`: neither its strip growth nor its first
derivative is forced to carry a factor `N`. The analogous `xi^(-1)` in the
scaled difference is cancelled by differentiation of `exp(-i*xi*z)`. Any
future fine/block conversion remains explicit, but an `N^5` loss may not be
introduced by treating this normalized average as an unnormalized
degree-`N` polynomial.

No complex variation estimate, strip radius, joint `B0`, contour shift or
regional-Green transport is claimed. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5ap normalized entire-average strip growth (SEALED; variation open)

Exact source checkpoint `0b5d26565740b110c8ef8e0216529c671914f88f`
passed cold GitHub Actions run
[`31250433443`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31250433443)
(workflow checkpoint `ed818e31f2c6a93cdbe992b43f97f5daaedb1f7a`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
warning-free focal completed 3,276 jobs, focal and audit exited zero, and all
five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The literal finite average is normalized before continuation:

```text
u_N(z) = N^(-1) * sum_{r < N} exp(-i*(r/N)*z).
```

The exact norm of the `r`-th summand is
`exp((r/N)*Im z)`. Since `0 <= r/N < 1`, every summand is bounded by
`exp(rho)` on `|Im z| <= rho`; the number of summands cancels exactly against
`N^(-1)`. Thus the one-coordinate bound `|u_N(z)| <= exp(rho)`, the
`d`-coordinate bound `|u_N(z)| <= exp(rho)^d`, and the holomorphic pairing
bound `|u_N(z)u_N(-z)| <= exp(rho)^(2d)` are all uniform in `N`.

This rules out the proposed `N`-bandwidth and `N^5` strip loss in the
normalized momentum variable. Fine/block units remain explicit, but they may
not be reintroduced through this average. The next brick is the corresponding
scale-uniform difference/derivative estimate; no complex denominator
variation, radius, `B0`, contour shift or regional-Green transport is claimed.
This is infrastructure below window 15: counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5aq normalized entire-average vertical variation (SEALED; denominator variation open)

Exact source checkpoint `bd392f4113bdae819b9f095003607091ca30e25e`
passed cold GitHub Actions run
[`31251069131`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31251069131)
(workflow checkpoint `e5cd02e0bfb5b336664f8478c0180accba994d58`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
warning-free focal completed 3,277 jobs, focal and audit exited zero, and all
five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

For a complex momentum `z`, the relevant comparison point is `(Re z : C)`,
not an arbitrary second complex momentum. The real momentum and reciprocal
alias then cancel before estimation. The exact exponent displacement is

```text
|(r/N) * (z - Re z)| = (r/N) * |Im z|,
```

and `r/N < 1`. Combining the exponential difference estimate with the
normalized finite sum gives the scale-uniform vertical bound

```text
|u_N(z) - u_N(Re z)| <= rho * exp(rho)
```

whenever `|Im z| <= rho`. Neither `N`, the real part of `z`, nor an alias
cardinality enters. The next endpoint telescopes this coordinatewise estimate
through the `d`-dimensional amplitude and its opposite-momentum pairing before
assembling the stabilized denominator. No denominator variation, radius,
`B0`, contour shift or regional-Green transport is claimed. Counters remain
`20/41`, `TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5ar coordinate-product and opposite-pair variation (SEALED; denominator variation open)

Exact source checkpoint `c2d64db27a268fbbbca661472e4d8b1310301848`
passed cold GitHub Actions run
[`31251690965`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31251690965)
(workflow checkpoint `1e40b054508be6b5bb533ae951d2a4f7405cac55`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
warning-free focal completed 3,278 jobs, focal and audit exited zero, and all
four audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

A generic finite-product telescope now turns factor bounds `|f_i|,|g_i|<=R`
and variations `|f_i-g_i|<=eps` into the explicit estimate

```text
|prod f_i - prod g_i| <= d * eps * R^d       (R >= 1).
```

With `R=exp(rho)` and `eps=rho*exp(rho)`, this gives a scale-uniform vertical
bound for the full `d`-coordinate CMP89 amplitude. A second product-rule
estimate bounds the holomorphic pair `u(z)u(-z)` against its real slice with
both contributions and both growth factors visible. The deliberately coarse
extra power of `exp(rho)` is isolated in the generic telescope; it may be
sharpened if the final scalar budget requires it, without changing the
one-coordinate producer.

No stabilized-denominator variation, complex nonvanishing radius, `B0`,
contour shift or regional-Green transport is claimed. This is infrastructure
below window 15: counters remain `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

### Step 7.5as entire fine-symbol vertical variation (SEALED; weighted alias quotient open)

Exact source checkpoint `f7ea5904ce33ba31c5b129bc717871f4ebb478bf`
passed cold GitHub Actions run
[`31252428842`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31252428842)
(workflow checkpoint `f51cddc2c4d82a87038ae8498611ef62a36474be`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
warning-free focal completed 3,281 jobs, focal and audit exited zero, and all
six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

For `0 < xi <= 1`, one entire scaled difference varies vertically by at most
`rho*exp(rho)`: the `xi` from the exponent cancels the quotient by `xi`.
Applying the product rule to opposite momenta and summing coordinates gives
the explicit bound

```text
sum_mu (rho*exp(rho)) * (2*|Re z_mu| + rho*exp(rho))
```

for `Delta^xi(z)-Delta^xi(Re z)`. The mass term cancels exactly. The real
momentum remains visible on purpose: replacing it by the diameter or
cardinality of the reciprocal-alias fibre would destroy the later uniform
sum.

This brick neither inverts a fine symbol nor treats the zero alias as
nonvanishing. The next source-facing step must preserve reciprocal-alias
decay in the variation of the averaging pair and combine it with the sealed
noncentral real gap. No stabilized-denominator variation, strip radius,
`B0`, contour shift or regional-Green estimate is claimed. Counters remain
`20/41`, `TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5at moment-dependent noncentral complex gap (SEALED; weighted alias quotient open)

Exact source checkpoint `eddb70d1da3f3aa5fb50414d68bd0c60313d78e2`
passed cold GitHub Actions run
[`31254402223`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31254402223)
(workflow checkpoint `cdf6b992d40ec65d9e7858de6ed9ae11ce27fd9b`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal ran from `11:12:43Z` to `11:28:13Z`, completed 8,430 jobs, and the audit
ended at `11:28:21Z`; both exited zero. All five audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`57c539234639e9d103276098c563c6be651886e413c4458cb8038af82176cac3`,
reproduced after downloading artifact `9021140614`; GitHub reports artifact
digest `8f018e848fd25cbe4e3e0c51d463a8d27701c728d2183ffcae75493ad54f3348`.

In dimension four, the exact `l1 <= 2*l2` comparison turns the sealed entire
fine-symbol variation into the moment-dependent budget

```text
eps * (4*|q|_2 + 4*eps),    eps = rho*exp(rho).
```

If that budget spends at most half of the real CMP89 lower bound
`(3*pi)^(-2)*|q|_2^2`, the complex fine symbol retains the other half. The
conditional lower theorem does not carry a redundant noncentrality premise;
a separate corollary uses `m != 0` to prove the lower bound is strictly
positive and hence the complex symbol is nonzero. The momentum dependence is
kept deliberately: replacing it by the global `1/9` before the quotient sum
would discard reciprocal-alias decay.

The strip parameter `rho` here is the imaginary displacement in the
normalized Brillouin-momentum variable used by the literal entire average and
scaled difference. Their `r/N` and `xi = 1/N` factors already cancel the
apparent bandwidth loss. The later fine/block spatial-rate conversion must be
a named Fourier/physical dictionary; this seal neither identifies `rho` with
the final `delta0` nor introduces an `N^5` factor mentally.

The first cold run `31253330707` was mathematically green but is retained only
as non-sealing evidence because the new module exposed a redundant `hm0`
premise. Diagnostic run `31254166319` then caught the missing explicit `mass`
specialization; cached run `31254286978` passed but retained PRE-VALIDATION.
Only the cold run above retires it.

No alias-weighted complex amplitude bound, quotient variation, stabilized
denominator radius, joint `B0`, contour shift or physical Green estimate is
proved. No terminal field is discharged: counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5au alias-weighted entire-average strip bound (SEALED; denominator radius open)

Exact source checkpoint `87ffa0b6a41a1201cfe32b3955f8c4345a05be62`
passed cold GitHub Actions run
[`31257291450`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31257291450)
(workflow checkpoint `f4a8ae30393d49f94765d674e3532685d6d8f5b4`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal ran from `12:29:33Z` to `12:30:12Z`, completed 3,292 jobs without a
source warning, and the audit ended at `12:30:20Z`; both exited zero. All
seven audited declarations use exactly `[propext, Classical.choice,
Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`dcfdcc9007b730278266b44704599b7bbe78a739749cc577b7437b9840e9be01`,
reproduced after downloading artifact `9021780151`; GitHub reports artifact
digest `6cb9eb351da10e71dacd3b08a4799eab135221d99bd5f0894e38837183943040`.

The finite geometric quotient now preserves one reciprocal-alias weight in
each coordinate throughout the normalized strip.  Its explicit condition is
`rho * exp rho <= 1/6`, and the product theorem retains the full
multidimensional weight without inserting the cardinality of the alias
fibre.  The `N^-1` in the real denominator is cancelled only against the
literal normalization of the average; it is not converted mentally into a
spatial decay rate.

Cold run `31256971974` is preserved as mathematically green evidence for the
previous source checkpoint, but it contained an `unnecessarySimpa` warning
and did not retire PRE-VALIDATION. Cached run `31257159057` verified the
warning-free source diagnostically; only the cold run above sealed it.

This brick does not assert that `rho * exp rho <= 1/6` is the binding physical
radius.  The noncentral complex-gap budget remains a separate condition, and
the sharper trigonometric floor is a later optional optimization rather than
part of this conservative producer. No stabilized-denominator radius, joint
`B0`, contour shift, Fourier/physical rate dictionary or regional-Green
estimate is proved. No terminal field is discharged: counters remain
`20/41`, `TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5av uniform noncentral complex radius (SEALED; stabilized sum open)

Exact source checkpoint `6d83d0ed7836df9ce831970f0703aa9f6863a024`
passed cold GitHub Actions run
[`31258180333`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31258180333)
(workflow checkpoint `a87f3dea04ca945bd4ebcce2d65917279ef2d1b9`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal ran from `12:53:06Z` to `13:03:41Z`, completed 8,431 jobs without a
source warning, and the audit ended at `13:03:45Z`; both exited zero. Both
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`a6b713fa5d383d93fe0ab83a5de6b55f088964299a26dc134a6ce4cb600152eb`,
reproduced after downloading artifact `9022131263`; GitHub reports artifact
digest `053272fb9ffcff6a5912f6a390113395bd5575dcd08e3231defa459976c8100d`.

The common noncentral strip condition is now one exact scalar inequality at
the nearest possible shifted Euclidean momentum, `|q|_2 = pi`. Monotonicity
then discharges the moment-dependent gap budget for every nonzero printed
alias without a family of hypotheses, an alias count, or an alias diameter.
This is a genuine uniform-radius producer below the stabilized denominator.

The producer intentionally consumes the already sealed conservative budget
`eps * (4*|q|_2 + 4*eps)`, `eps = rho*exp(rho)`. Therefore the sharper
engineering estimate `rho about 8.8e-3` is not yet a theorem of this route;
it requires a separate sharpening of the opposite-momentum pair variation.
The amplitude condition `eps <= 1/6` remains a distinct scalar condition.

No summation of complex noncentral quotients, stabilized-denominator lower
bound, joint `B0`, contour shift, Fourier/physical rate dictionary or
regional-Green estimate is proved. No terminal field is discharged: counters
remain `20/41`, `TermSource = 0`, and window 15 compatible but unattained.

Runs `31237719609` and `31237880610` preserve the two elaboration failures
(over-eager quotient decomposition, then the `Nat.cast_pow` dictionary).
Cached diagnostic run `31238006531` passed but retained PRE-VALIDATION; only
the cold run above retired it.

### Step 7.5aw complex noncentral alias quotient (SEALED; finite sum open)

Exact source checkpoint `ff09dc112b01d51a5640852a0cc8e1f817862fd3`
passed cold GitHub Actions run
[`31259452871`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31259452871)
(workflow checkpoint `19c58d1f9feb2d4c918ccf6c14102fb3c30603c3`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal ran from `13:25:56Z` to `13:41:39Z`, completed 8,433 jobs without a
source warning, and the audit ended at `13:41:47Z`; both exited zero. All
three audited declarations use exactly `[propext, Classical.choice,
Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`98cc354f59e7d65d5d0856e49ed1a51d3693589c0a9bb680ff767182a649507b`,
reproduced after downloading artifact `9022536472`; GitHub reports artifact
digest `7a2fd37533e23a2aa233c29b6b772916f6cdbff6936486870ca161721cb6fcef`.

One side of the physical opposite-momentum average pair now retains the
reciprocal-alias weight, while the other uses only the uniform strip-growth
bound. This avoids a false negation-invariance assumption for the half-open
even alias interval. The noncentral complex gap contributes the literal
radial factor `|q|_2^(-2)`, and the already sealed CMP89 (2.51)
redistribution at `alpha=-1` turns it into a summable product weight.

The two scalar conditions remain separate: `rho*exp(rho) <= 1/6` controls the
amplitude, while `CMP89Eq249UniformNoncentralComplexRadiusCondition rho`
controls the complex fine-symbol gap. The seal intentionally retains the
conservative factor-four gap budget; the proposed factor-two sharpening is
not imported.

Runs `31259057786` and `31259202883` preserve respectively the two explicit
constant-positivity failures and the last opaque radial-constant sign goal.
Cached diagnostic run `31259339067` passed but retained PRE-VALIDATION; only
the cold run above retired it.

No finite complex alias sum, stabilized-denominator lower bound, joint `B0`,
contour shift, Fourier/physical rate dictionary or regional-Green estimate
is proved. No terminal field is discharged: counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5ax finite complex noncentral alias sum (SEALED; stabilized denominator open)

Exact source checkpoint `832d014a7b3c5558c7b1a8f4821fa22ed5bdc06d`
passed cold GitHub Actions run
[`31260422445`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31260422445)
(workflow checkpoint `2a6f1e12d06d90a69a18c4aa14eb57824fc58545`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal ran from `13:50:40Z` to `14:06:52Z`, completed 8,434 jobs, and the audit
ended at `14:06:58Z`; both exited zero. The audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`bcf943221f5468385448777008c5de778d4f8f37c3529474d777fc404cdcd221`,
reproduced after downloading artifact `9022811583`; GitHub reports artifact
digest `eaff20526a79962161326dc8b3b51e3bcb9f2a62fc3484a451cb2cab9d3b5d05`.

The literal finite noncentral complex alias sum is now bounded uniformly in
`L^j`. The proof removes the central alias, sums the pointwise product weight,
and applies the exact four-dimensional product/tsum bound at `alpha=-1`.
No alias cardinality or diameter is inserted, and the two scalar strip
conditions remain separate.

Cached diagnostic run `31260306510` passed but retained PRE-VALIDATION; only
the cold run above retired it. No stabilized-denominator lower bound, joint
`B0`, contour shift, Fourier/physical rate dictionary or regional-Green
estimate is proved. No terminal field is discharged: counters remain
`20/41`, `TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5ay alias-weighted opposite-pair vertical variation (SEALED; quotient variation open)

Exact source checkpoint `4f9b86adf7428ead68c159daff0cea3ff50e2b0b`
passed cold GitHub Actions run
[`31261770494`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31261770494)
(workflow checkpoint `eb31362a75c49e0df072e8c96a8e4bf8197a2270`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal ran from `14:23:53Z` to `14:24:36Z`, completed 3,296 jobs, and the audit
ended at `14:24:42Z`; both exited zero. All four audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`45b58ffcf2c75b0558d80a07d155db4ebe58ad3836de739b74b5cc9550a2bcaa`,
reproduced after downloading artifact `9023011164`; GitHub reports artifact
digest `bb69974e17ec179c4f7dc31a2dc79afc201522e7da8c77564cb1f1e6b2d10d19`.

The producer exposes the normalized coordinate-zone premise beneath the
existing product strip bound, proves the literal CMP89 (2.51) product weight
even under alias negation, and retains one such weight while varying the
opposite-momentum averaging pair to its real slice.

The construction does **not** assert that the half-open centered alias set is
stable under negation: the opposite factor is estimated at `(-p,-m)` only
after the coordinate-zone premise has been separated from fibre membership.
No quotient variation, stabilized-denominator lower bound, joint `B0`, contour
shift, Fourier/physical rate dictionary or regional-Green estimate is claimed.
In particular, this seal does not replace the conservative factor-four
fine-symbol gap budget by the proposed factor-two sharpening. Diagnostic run
`31261520329` preserves the explicit real-slice elaboration failure; cached
run `31261659772` passed but retained PRE-VALIDATION. Only the cold run above
retired it.
No terminal field is discharged: counters remain `20/41`, `TermSource = 0`,
and window 15 compatible but unattained.

### Step 7.5az complex noncentral quotient vertical variation (SEALED; radial redistribution and finite sum open)

Exact source checkpoint `acf4b2b5a6afd21c1a09eb214580c757c6f33b4d`
passed cold GitHub Actions run
[`31262412986`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31262412986)
(workflow checkpoint `0cc33c1181e23f5299f726da04c4398eec539f70`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were skipped. The
focal ran from `14:39:48Z` to `14:52:24Z`, completed 8,435 jobs, and the audit
ended at `14:52:29Z`; both exited zero. All three audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic inner evidence archive has SHA-256
`1c7041b0ac53bfa3eb4cb80ad61af2b4d87bd04356d7a62c38551e7731a3f776`,
reproduced after downloading artifact `9023321573`; GitHub reports artifact
digest `dc2ce45d89736d2772a950d3de7f4279ce8ce43b047f052e4df046b8727f7787`.

The producer combines the sealed weighted averaging-pair variation with the
common moment-dependent gap at the complex point and its real slice.
Numerator variation pays one inverse gap and denominator variation pays two;
both terms retain the literal alias weight and the latter keeps the complete
fine-symbol variation budget visible.

No radial-power redistribution, finite quotient-variation sum, stabilized
denominator lower bound, joint `B0`, contour shift or physical Green estimate
is claimed. Failed diagnostic run `31262139783` preserves two missing
definitional unfoldings and one missing type annotation; cached run
`31262301181` passed but retained PRE-VALIDATION. Only the cold run above
retired it. The conservative factor-four gap budget remains unchanged.
No terminal field is discharged: counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5ba uniform vertical variation of the finite noncentral alias sum (SEALED)

Exact source checkpoint `8ec5b66891e54bd73859591608aace7d100f618e`
passed cold GitHub Actions run
[`31263911984`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31263911984)
under workflow checkpoint `94787dd73ee0c9e729075012a2753b60d84e24da`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,437 jobs and the focal/audit both exited
zero; both audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed producer inserts the
literal fine-symbol budget into the two-gap quotient estimate, relaxes the
resulting `|q|_2^(-3)` term to `|q|_2^(-2)` only after proving
`|q|_2 >= pi > 1`, and applies the existing `alpha=-1` source-weight
redistribution once. It then sums the finite alias fibre by the sealed product
tsum, without a cardinality factor.

No optimized trigonometric gap or factor-two fine-symbol variation is used.
No stabilized-denominator lower bound, joint `B0`, contour shift or physical
Green estimate is claimed. Cached run `31263756123` is diagnostic only; failed
runs `31263405769` and `31263602897` preserve the two elaboration frontiers.
No terminal field is discharged: counters remain
`20/41`, `TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5bb stabilized denominator vertical variation (SEALED; complex floor open)

Exact source checkpoint `a71e5d5cceaa20971bf40fe8959c5bc4c3737978`
passed cold GitHub Actions run
[`31265445387`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31265445387)
under workflow checkpoint `596751872e8b55150df95e662b4eb1de81333c9d`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,439 jobs and the focal/audit both exited
zero; all three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed producer expands the
three literal branches of the stabilized CMP89 (2.49) denominator before
estimation. It combines the sealed central fine-symbol variation, central
averaging-pair variation, complex noncentral sum bound and noncentral sum
variation. The product branch keeps the fine-symbol and alias-sum costs
separate.

The source window `mass^2 <= 1` remains an explicit input. No optimized
trigonometric gap or factor-two fine-symbol variation is imported. No complex
lower bound, reciprocal `B0`, contour shift, Fourier/physical rate dictionary
or regional-Green estimate is claimed. No terminal field is discharged:
counters remain `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.

### Step 7.5bc complex stabilized floor and reciprocal (SEALED; scalar attainment open)

Exact source checkpoint `4f62edc183ceac0fde4b7b2b847f2270f458545b`
passed cold GitHub Actions run
[`31266722921`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31266722921)
under workflow checkpoint `86468c64ce33632a38066c8057496f92449f3c34`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,440 jobs and the focal/audit both exited
zero; all three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed endpoint names the single scalar comparison
`stabilizedVariationBound(a,rho) < stabilizedRealFloor(a)`. Under that window,
the reverse triangle inequality gives a positive complex floor, literal
nonvanishing and an explicit reciprocal bound throughout the common strip.
Cached run `31266584461` is diagnostic only. Failed diagnostic run
`31266441511` preserves the redundant reduction and inverse-orientation
errors; their repair changed neither the statement nor any scalar constant.

This reduces the remaining analytic question to a scalar target; it does not
prove that the source flow attains it. The source window `mass^2 <= 1` remains
an explicit input, and neither the sharper trigonometric gap nor the proposed
factor-two vertical variation is imported. No contour shift,
Fourier/physical rate dictionary, regional-Green estimate, physical `B0` or
window-15 contraction is claimed. No terminal field is discharged: counters
remain `20/41`, `TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5bd positive common stabilized radius (SEALED)

The proposed producer proves continuity at zero of the complete stabilized
variation majorant and its exact value zero there. Since the real floor is
strictly positive for every `a > 0`, the amplitude budget, noncentral complex
gap and stabilized complex-floor window hold simultaneously at some common
`rho > 0`.

This is non-vacuity of the existing conservative scalar regime, not a
numerical optimization. Neither the sharper trigonometric gap nor the
factor-two vertical variation is used. The source condition `mass^2 <= 1`,
the complete complex integrand, contour shift, Fourier/physical rate
dictionary, physical `B0` and window-15 contraction remain open. No terminal
field is discharged: counters remain `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

Exact source checkpoint `d88c6b1f58882c88189c9fe67e40c6f763faab84`
passed cold GitHub Actions run `31269362634` with workflow checkpoint
`fa1cbd7d84ae6274407df92665f8c72de58810a3`. Restore and save of
`.lake/build` were both skipped. The focal completed 8,441 jobs; focal and
audit exited zero, and all three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`. The deterministic evidence archive
has SHA-256 `da04f8268ced8357835a392213ae753731c1a0eb663bbc1223184e93fdf8a061`.

The seal establishes existence of one positive scalar radius satisfying the
three conservative strip budgets simultaneously. It does not choose a
numerical radius, discharge the flowing `mass^2 <= 1` source condition,
construct the complete complex integrand or physical `B0`, or attain window
15. No terminal counter moves.

### Step 7.5be assembled stabilized complex integrand (SEALED; uniform strip bound open)

The proposed producer transcribes the complete finite complex integrand under
CMP89 (2.49), keeping the Holder and transport phases, the signed scaled
difference, normalized averaging amplitude, unit-lattice symbol and every
fine-alias denominator literal. It then constructs the removable extension
with one common stabilized denominator:

```text
central bare numerator
  + Delta_0 * sum_{m != 0} bareNumerator_m / Delta_m.
```

The equality with the printed rational expression is stated only on its
original domain (`Delta^1`, the reduced denominator and every `Delta_m`
nonzero). The stabilized expression itself does not require the two central
nonvanishing assumptions. No bound or family of integrands is accepted as an
input.

This is the missing algebraic assembly before the strip estimate, not the
strip estimate itself. Noncentral complex nonvanishing, the flowing
`mass^2 <= 1` condition, the physical `B0`, contour shift,
Fourier/physical-rate dictionary and window 15 remain open. No terminal field
is discharged: counters remain `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

Exact source checkpoint `fa607d1bb5bed6460c4c852510d2a1cbf538aecc`
passed cold GitHub Actions run `31271086914` with workflow checkpoint
`f47d4903c0b2ba241f15d76954dd301c9d738d1d`. Restore and save of
`.lake/build` were both skipped. The focal completed 8,442 jobs; focal and
audit exited zero, and all ten audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`. The deterministic evidence archive
has SHA-256 `77db53fa9cb7a99c7ad4513e91a80d6d5a57e638dfa75b4299db401115ea1a62`.

The seal proves that the literal printed rational integrand equals the
assembled stabilized expression on the original rational domain. The central
branch has no fine-symbol quotient, every noncentral branch retains the
literal `Delta_0 / Delta_m` ratio, and both use the common stabilized
denominator. The stabilized object therefore exists at the two removable
central zeros without assuming those two nonvanishing conditions.

It does **not** prove the noncentral strip from the positive-radius source,
bound the complex numerator, construct `B0`, justify a contour displacement,
identify the Fourier and physical rates, resolve the flowing mass condition,
or attain window 15. The live counters remain exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5bf complex contour-phase dictionary (SEALED; endpoint-specific contour displacement open)

Exact source checkpoint `e0b32533411b5ff8be5d55d432d076a7ca7172ae`
passed cold GitHub Actions run
[`31273452649`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31273452649)
with workflow checkpoint `210a709656d6f7ce6afb8abf16392d49218a93b6`.
The job recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. Dependency materialization ran from `19:03:26Z` to `19:04:56Z`; the
focal then ran to `19:21:37Z`, completed 8,443 jobs, and the audit ended at
`19:21:45Z`. Focal and audit both exited zero. All ten audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9026527828`, named
`cmp89-complex-contour-phase-e0b32533411b5ff8be5d55d432d076a7ca7172ae`,
has GitHub digest
`68142bfe121c234aaffab19067dd478d4296300297320f76050908fa923e1a92`.
The deterministic inner archive re-hashed on Windows to
`afdc0cd592aa11512c92c4ade4ab2e9e06d76808d8731695a323edd42f477efe`,
identical to the hash recorded inside the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed producer rewrites the two phase factors in the stabilized
CMP89 (2.49) numerator exactly as

```text
(exp(i q.(x-x')) - 1) * exp(i q.(x'-y))
  = exp(i q.(x-y)) - exp(i q.(x'-y)).
```

It also proves that reciprocal aliases do not alter the imaginary part of a
phase and derives the explicit coordinate-strip growth
`exp(rho * |displacement|_1)` for each endpoint. No phase-bound family or
spatial constant is supplied as input. The final source removes two unused
`0 <= rho` premises rather than suppressing the linter; cached diagnostic run
`31273316298` verified that stronger interface before the cold seal. Earlier
cold run `31272522509` remains preserved as a compiler-green but unsealed run
because it exposed the unused-premise warning.

This is the exact dictionary required before the source contour can be split
or displaced. It does not choose a contour direction, prove uniform spatial
decay, bound the complete stabilized numerator, construct `B0`, resolve the
flowing mass condition or attain window 15. In particular it consumes only
the conservative strip already compiled in the tree: neither the optional
8x trigonometric sharpening nor the uncompiled 2x opposite-pair variation is
used or claimed. No terminal field is discharged: counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

### Step 7.5bg signed endpoint contour momentum (SEALED; contour deformation open)

Exact source checkpoint `8490998241b445e519a401db1bb6af523b4eeb2b`
passed cold GitHub Actions run
[`31274961427`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31274961427)
with workflow checkpoint `9f8b321da33e399651fd3dd9f5ea03cbdf589259`.
The job recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. Dependency materialization ran from `19:39:52Z` to `19:41:16Z`; the
focal then ran to `19:52:14Z`, completed 8,444 jobs, and the audit ended at
`19:52:19Z`. Focal and audit both exited zero. All six audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9026870452`, named
`cmp89-signed-contour-phase-8490998241b445e519a401db1bb6af523b4eeb2b`,
has GitHub digest
`c6b0b7ff8f180a1e106e7df81e1f23b68466c73712678f026982dac6e05fc1b2`.
The deterministic inner archive re-hashed on Windows to
`15690f63c1e1a65704e586630ee117cdc6f9fda69f68fa4028511b757decf038`,
identical to the hash recorded inside the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed producer assigns one endpoint displacement `u` the literal
complex momentum

```text
z_mu = p_mu + i * rho * sign(u_mu).
```

It proves coordinatewise strip membership and the exact alias-independent
identity

```text
|exp(i (z + 2*pi*m).u)| = exp(-rho * |u|_1).
```

This construction is endpoint-specific. The two phases exposed by Step 7.5bf
must be shifted separately after splitting the integral; no single shift of
their difference is asserted. The equality between the original and shifted
integrals, the complete strip bound, physical `B0`, flowing `mass^2 <= 1`
dictionary, Fourier/physical-rate transport and window-15 contraction remain
open. Neither optional constant sharpening is consumed. No terminal field is
discharged: counters remain `20/41`, `TermSource = 0`, and window 15 compatible
but unattained.

Diagnostic runs `31274463630` and `31274640242` preserved the missing
`SignType` import/namespace failures. Cached run `31274809925` then passed the
qualified source but retained PRE-VALIDATION; only the cold run above retired
it. These were elaboration repairs and changed no contour formula, constant or
claim.

### Step 7.5bh periodic holomorphic vertical shift (SEALED infrastructure; physical periodicity open)

Exact source checkpoint `94e7b193304c65ec8aae5c4026056109b9b8c281`
passed cold GitHub Actions run
[`31276160414`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31276160414)
with workflow checkpoint `1db7856bcdd37fa68827897178272679619d42a7`.
The job recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. Dependency materialization ran from `20:08:37Z` to `20:10:00Z`; the
focal then ran from `20:10:06Z` to `20:10:10Z`, completed 2,743 jobs, and the
audit ended at `20:10:15Z`. Focal and audit both exited zero. The audited
declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9027072555`, named
`periodic-holomorphic-vertical-shift-94e7b193304c65ec8aae5c4026056109b9b8c281`,
has GitHub digest
`5eacebf4810340aa6d8a30b79a6089f41fd36782173d1df15c77022197e33d5f`.
The deterministic inner archive re-hashed on Windows to
`64233520d467be7aae3d6cc20c60a9752149edb06366e7f73af082bc1d9019bb`,
identical to the hash recorded by the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed theorem derives equality of the interval integral on `[0,T]` and
its vertical translate by `eta*I` from complex differentiability on the
closed rectangle and literal period `T`. It invokes the rectangular Cauchy
theorem and cancels the vertical sides by periodicity; equality of the two
horizontal integrals is not accepted as an input. Neither a sign condition on
`T` nor one on `eta` is needed.

This is the generic one-coordinate contour engine, not the physical CMP89
contour deformation. The stabilized finite alias sum must still be shown
holomorphic and periodic under the physical `2*pi` shift. That periodicity is
a reindexing of the finite alias fibre, not a termwise identity, and the
stabilized extension separately singles out the central branch. Coordinate
iteration, the complete strip bound, `B0`, the flowing `mass^2 <= 1`
dictionary, Fourier/physical-rate transport and window 15 remain open. No
terminal field is discharged: counters remain `20/41`, `TermSource = 0`, and
window 15 compatible but unattained.

Cached diagnostic run `31276018596` passed after the sole elaboration repair:
the real and imaginary coordinates of the Cauchy rectangle endpoint had to be
normalized before rewriting the vertical integral. Earlier run `31275860871`
preserves that failed rewrite. Neither run changed the theorem statement or
introduced an analytic hypothesis.

### Step 7.5bi unit-lattice endpoint phase wrap (SEALED; finite-fibre reindexing open)

Exact source checkpoint `1a610d23fd2886f4c3be5dee27153c5f8f59402c`
passed cold GitHub Actions run
[`31276699439`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31276699439)
with workflow checkpoint `c26d21507edcd2af4563c01449987b1e733e7f4e`.
The job recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. Dependency materialization ran from `20:21:41Z` to `20:23:08Z`; the
focal ran from `20:23:13Z` to `20:40:43Z`, completed 8,445 jobs, and the audit
ended at `20:40:49Z`. Focal and audit both exited zero. All four audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9027422768`, named
`cmp89-lattice-phase-periodicity-1a610d23fd2886f4c3be5dee27153c5f8f59402c`,
has GitHub digest
`3df4d6303db77034043bfae319b1866c769f860eb73d8e31a364de67fc008590`.
The deterministic inner archive re-hashed on Windows to
`03b83a337d377e23c26939dab72eca01b6ab52f6ddb97874d8d57f6b49a8faf3`,
identical to the hash recorded by the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed source embeds a literal unit-lattice displacement
`u : Fin d -> Int` into the real phase coordinates and adds one full alias
period `2*pi*N` to a chosen complex momentum coordinate. It proves the exact
phase increment `2*pi*N*u_mu` and derives invariance of the endpoint
exponential from `exp(n*2*pi*I)=1`. Periodicity is therefore a theorem from
the lattice data, not a supplied family.

This closes only the phase factor under a boundary wrap. Periodicity of the
complete stabilized CMP89 integrand still requires a permutation of the
centered finite alias fibre and periodicity of the averaging, Laplacian and
stabilized-denominator factors. The source-to-tree dictionary producing the
integer endpoint displacements from the physical lattice sites also remains
to be installed at the final specialization. No integral, `B0`, Fourier-rate
dictionary or window-15 producer is claimed. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31276564821` passed the same source before the cold
seal. It required no elaboration repair and introduced no new scalar window.

### Step 7.5bj signed-lattice `l1` exponential summation (SEALED; physical owner dictionary open)

Exact source checkpoint `5ecbb510ba413443374c47bc732f6137f9008810`
passed cold GitHub Actions run
[`31278070364`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31278070364)
with workflow checkpoint `464799b71683a780338de1e9ebc43b736be2e2c9`.
The job recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. Dependency materialization ran from `20:55:50Z` to `20:57:15Z`; the
focal ran from `20:57:15Z` to `20:57:37Z`, completed 3,283 jobs, and the audit
ended at `20:57:42Z`. Focal and audit both exited zero. All six audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9027612767`, named
`cmp89-signed-lattice-l1-exponential-sum-5ecbb510ba413443374c47bc732f6137f9008810`,
has GitHub digest
`e77fad76e9ce6994df89f3754a3fb5aaa14669ae14b9157f9c8caf87afaa4ba5`.
The deterministic inner archive re-hashed on Windows to
`11c4f287d9a303988a0e9f2047b20ef572cf6b5489fe0248218828c71fbee670`,
identical to the hash recorded by the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed source evaluates the literal one-coordinate spatial weight
`exp(-delta * natAbs n)` on all of `Int` as
`(1 + exp(-delta)) / (1 - exp(-delta))`. It then factorizes every finite
centered `d`-coordinate box exactly and bounds it uniformly by the `d`-th
power of that geometric constant. Thus the signed `l1` decay retains the
`delta^(-d)` scale instead of paying the existing ball-counting
`delta^(-(d+1))` majorant. No infinite-dimensional Fubini identity is claimed:
the proved consumer-facing statement is the uniform bound for every finite
centered box.

This quantitative improvement is not yet connected to the physical owner
displacements or the complete stabilized CMP89 integrand. The finite-alias
wrap, physical owner-to-integer dictionary, `B0`, Fourier/physical-rate bridge
and window-15 contraction remain open. The optional `8x` and `2x` radius
sharpenings are not consumed. No terminal field is discharged: counters
remain `20/41`, `TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31277952998` passed the same source before the cold
seal. Failed run `31277793979` preserves the earlier elaboration errors:
local `let` values were incorrectly used as rewrite equations, and the
negative-integer branch needed the literal normal form `-((n : Int) + 1)`.
The repair changed no statement, constant or hypothesis.

### Step 7.5bk centered reciprocal-alias cycle (SEALED; vector reindexing and physical periodicity open)

Exact source checkpoint `b962f9a77e6523326a26474ac323b2912f755c71`
passed cold GitHub Actions run
[`31279450837`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31279450837)
with workflow checkpoint `4a010f5ab19c6482ec5cb906a425352b8f767c21`.
The job recorded `COLD_MODE=true`; restore and save of `.lake/build` were both
skipped. Dependency materialization ended at `21:31:48Z`; the focal ran from
`21:31:53Z` to `21:32:10Z`, completed 3,278 jobs, and the audit ended at
`21:32:13Z`. Focal and audit both exited zero. All six audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9028002537`, named
`cmp89-centered-alias-cycle-b962f9a77e6523326a26474ac323b2912f755c71`,
has GitHub digest
`388d2c7a5839fcf52b28b9f52c1fb82bbb6e0d2c25b419ff94681ab93977cc45`.
The deterministic inner archive re-hashed on Windows to
`059d073ce2cc779465850790dfde01279db44a678d6e5cfdcd8c441b75c5faff`,
identical to the hash recorded by the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed brick proves that the odd/even representative set printed in
CMP89 (2.45) is uniformly the half-open interval of `N` consecutive integers
beginning at `-floor(N/2)`. It constructs explicit successor and predecessor
maps, proves them inverse, and packages the successor as a cyclic permutation.
The wrap is not hidden: the output is either `m+1`, or adding the literal
alias count `N` to the wrapped output recovers `m+1`.

This is the coordinate fibre permutation required by the physical `2*pi`
boundary shift. It does not yet lift the cycle to one coordinate of the
`d`-dimensional alias vectors, reindex a finite sum, transport the averaging,
Laplacian, denominator and endpoint phase factors, or prove periodicity of
the complete stabilized integrand. No `B0`, physical rate, window-15
attainment or terminal field is produced. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31279345615` passed before the cold seal. Failed runs
`31278649551`, `31278803693`, `31278940403`, and `31279212640` preserve the
dependent-membership rewrite, subtype-projection normalization, and misplaced
`else` repairs. None changed the representative set, cycle, constant or
hypothesis.

### Step 7.5bl centered reciprocal-alias vector cycle (SEALED; physical factor transport open)

Exact source checkpoint `9eafb8a3ef443dd33aea42a85a68d424f3500022`
passed cold GitHub Actions run
[`31280050123`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31280050123)
with workflow checkpoint `f5cd0b41122a929fc8dd328cc0f4bb315d7a03ca`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. Dependency materialization ran from `21:45:11Z` to
`21:46:41Z`; the focal ran from `21:46:41Z` to `21:47:00Z`, completed 3,279
jobs, and the audit ended at `21:47:03Z`. Focal and audit both exited zero.
All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9028167606`, named
`cmp89-centered-alias-vector-cycle-9eafb8a3ef443dd33aea42a85a68d424f3500022`,
has GitHub digest
`dc99ebab2efdba73580f3bb94480c187700b84862adaf06ffe379de00c3de752`.
The deterministic inner archive re-hashed on Windows to
`77d581fb085d64469092051c5f9b836bbca68e133d3c436c2bb16cf1418b10d7`,
identical to the hash recorded by the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed brick identifies the printed `d`-coordinate alias fibre with the
dependent product of the scalar centered fibres and conjugates the already
sealed scalar cycle into a permutation of that literal finite vector fibre.
The chosen coordinate advances by one with the wrap by `N` still explicit;
every other coordinate is fixed. A generic `Equiv.sum_comp` endpoint then
reindexes finite sums over the fibre without postulating pointwise `2*pi`
periodicity of one alias term.

This is algebraic reindexing only. The averaging amplitude, fine and unit
Laplacians, denominator and endpoint phases still require transport under the
physical shift, and the central/noncentral split means global periodicity of
the stabilized extension is not inferred from the permutation alone. The
safe route remains: prove periodicity of the displayed integrand on its
non-singular domain, then use its sealed equality with the stabilized
extension at both boundary points. No `B0`, physical rate, window-15
attainment or terminal field is produced. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31279938081` passed before the cold seal. Failed run
`31279799675` preserves the sole elaboration repair: subtype membership had
to be changed definitionally to the literal `piFinset` before applying
`Fintype.mem_piFinset`. The representative set, permutation, sum theorem and
hypotheses were unchanged.

### Step 7.5bm physical-period alias-momentum transport (SEALED; concrete factor periods open)

Exact source checkpoint `41981f8e6b7cb547d92468563a807c2bacd1c76b`
passed cold GitHub Actions run
[`31280717065`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31280717065)
with workflow checkpoint `d774364717c19ce079a58265eebe1fadce5f56d0`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. Dependency materialization ran from `22:01:47Z` to
`22:03:17Z`; the focal ran from `22:03:17Z` to `22:19:57Z`, completed 8,448
jobs, and the audit ended at `22:20:03Z`. Focal and audit both exited zero.
All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9028532922`, named
`cmp89-alias-momentum-cycle-41981f8e6b7cb547d92468563a807c2bacd1c76b`,
has GitHub digest
`70ee0c0573376f125c61bcb3a3c6ac44fbec88aa8953da8c96a13671d77f4c8d`.
The deterministic inner archive re-hashed on Windows to
`4b14eba43de9e961fc7f1b1090f250d5d888102bab62a71eea0dbeb1b298dbdd`,
identical to the hash recorded by the cold runner; all 13 entries of its
`SHA256SUMS` manifest also re-hashed exactly.

The sealed theorem shifts a physical momentum coordinate by the literal
Brillouin period `2*pi` and proves that each resulting alias momentum is
either the momentum at the cycled representative or its explicit
`2*pi*N` pointwise-period translate at the wrap. A generic factor with an
already proved `2*pi*N` period is therefore transported to the cycled alias,
and both subtype and literal-finset sums are reindexed exactly.

The pointwise period remains an input to the generic endpoint, not a renamed
physical conclusion. Separate producers are still required for the entire
average, fine Laplacian and their pairings; the unit Laplacian has the
different physical period `2*pi`. The complete denominator and displayed
integrand periodicity remain open, as does transfer to the stabilized
extension on its non-singular domain. No `B0`, physical-rate bridge,
window-15 attainment or terminal field is produced. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31280585168` passed before the cold seal. Failed run
`31280430141` preserves the two purely elaborational repairs: the coefficient
orientation in `linear_combination` and the explicit `Finset.sum_coe_sort`
bridge. Neither changed the physical shift, wrap disjunction, periods,
finite fibre or hypotheses.

### Step 7.5bn entire averaging-factor alias period (SEALED; fine Laplacian period open)

Exact source checkpoint `7fac9d795b7588160abe325eb2ee724044e33881`
passed cold GitHub Actions run
[`31281971984`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31281971984)
with workflow checkpoint `191f953bf6bf0408ed050d97010162a9e7250564`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `22:35:22Z` to `22:51:18Z`, completed
8,446 jobs, and the audit ended at `22:51:24Z`. Focal and audit both exited
zero. All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9028880249`, named
`cmp89-entire-average-periodicity-7fac9d795b7588160abe325eb2ee724044e33881`,
has GitHub digest
`c0ab505fa56be5a446b459a013e5c4265d22f0c1ba1bae106fd899cd993b9458`.
The deterministic inner archive re-hashed on Windows to
`1110860dab97fe2d7a69d66f930eb5769017af99ed7c0c599b67b2e0b76ba05f`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed brick derives the exact `2*pi*N` period from the finite geometric
continuation itself, for every integer multiple. It lifts the scalar period
to one coordinate of the complete averaging amplitude, proves the matching
negative wrap at opposite momentum, and concludes invariance of the literal
holomorphic pairing `u(z) * u(-z)`. No periodicity family is accepted as an
input.

This is the fine-lattice averaging factor only. The fine Laplacian at
`xi = 1/N`, its quotient, the unit Laplacian at the distinct physical period
`2*pi`, the complete denominator and displayed-integrand periodicity remain
open. Transfer to the stabilized extension still requires the sealed
displayed/stabilized equality on the non-singular domain. No `B0`, rate,
window-15 attainment or terminal field is produced. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31281856879` passed before the cold seal. Failed run
`31281679586` preserves the sole mechanical repair: the negative wrap
normalized `-z-period` versus `-period-z` by commutativity. The theorem
statement, period, factor and hypotheses were unchanged.

### Step 7.5bo entire fine-Laplacian alias period (SEALED; quotient transport open)

Exact source checkpoint `b38d7f1226fa68be399bea0f972fe3ddaf9bf040`
passed cold GitHub Actions run
[`31282931967`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31282931967)
with workflow checkpoint `652019b0b9ccb3fdb1cc9bad2400a1a6f1660a15`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `23:00:43Z` to `23:18:05Z`, completed
8,447 jobs, and the audit ended at `23:18:11Z`. Focal and audit both exited
zero. All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9029160130`, named
`cmp89-fine-laplacian-periodicity-b38d7f1226fa68be399bea0f972fe3ddaf9bf040`,
has GitHub digest
`64e1b94abed0803fc324c88dd3512a89a1093af1c11de1dccb77360701fd2177`.
The deterministic inner archive re-hashed on Windows to
`8c92c8993e7bf8e2b42ca945bd60b9f0f234e6b7e165979ae52adf21cef6bf37`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed brick derives the `2*pi*N` period of the entire scaled difference
at the literal inverse spacing `xi = 1/N`, proves the matching
opposite-momentum product, and lifts it coordinatewise to the complete fine
Laplacian symbol including its mass term. The exponential cycle is inherited
from the already sealed finite-average base; no period is postulated.

The average and fine-Laplacian periods are now both produced, but their
quotient has not yet been specialized to `N = L^j` or fed through the alias
permutation. The unit Laplacian still needs its different `2*pi` period, and
complete denominator/displayed-integrand periodicity plus transfer to the
stabilized extension remain open. No `B0`, rate, window-15 attainment or
terminal field is produced. Counters remain `20/41`, `TermSource = 0`, and
window 15 compatible but unattained.

Cached diagnostic run `31282807973` passed before the cold seal. No failed
Lean run was needed for this brick; its first compiler execution accepted
the statement, scale and proof unchanged.

### Step 7.5bp complete complex-denominator physical period (SEALED; displayed integrand open)

Exact source checkpoint `e631885ae3dcb38bf71bdc73d2c2e241a99c32c8`
passed cold GitHub Actions run
[`31283934356`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31283934356)
with workflow checkpoint `79502bf53dc193cae6dcc084edec84aa442252d4`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `23:27:17Z` to `23:44:56Z`, completed
8,451 jobs, and the audit ended at `23:45:03Z`. Focal and audit both exited
zero. All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9029429431`, named
`cmp89-complex-denominator-periodicity-e631885ae3dcb38bf71bdc73d2c2e241a99c32c8`,
has GitHub digest
`7d27c56ff46cd04e22e199f0fe39c10deee0f64a14fa825137955e28b374174e`.
The deterministic inner archive re-hashed on Windows to
`0035007110ff5dc299872306c41ffd17a97884562b729d7ed8b03815af563530`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed brick names the literal average/fine-Laplacian quotient, proves
its pointwise `2*pi*N` period, specializes the sole cast dictionary at
`N=L^j`, and transports the full centered alias sum under a physical `2*pi`
shift by exact permutation. It separately proves the `2*pi` period of the
unit-lattice Laplacian and composes both results into physical periodicity of
the complete multiplied complex denominator in CMP89 (2.49).

No denominator nonvanishing is inferred from periodicity, and no numerator
or endpoint-phase periodicity is bundled into this result. The next safe
endpoint is the displayed finite integrand on its non-singular domain;
transfer to the stabilized extension must then use the already sealed
displayed/stabilized equality at both boundary points. No `B0`, rate,
window-15 attainment or terminal field is produced. Counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31283828202` passed before the cold seal. No failed
Lean run was required: the quotient, cast specialization, fibre reindexing
and two distinct physical periods compiled on their first execution.

### Step 7.5bq displayed/stabilized integrand physical period (SEALED; contour integration open)

Exact source checkpoint `747e7c6d892ed7c6bbabb0488ca3bfd87c101af0`
passed cold GitHub Actions run
[`31285123749`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31285123749)
with workflow checkpoint `6ef911e2e7e83e6e6c0de99a67d7b42970212e70`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `23:59:15Z` to `00:16:16Z`, completed
8,452 jobs, and the audit ended at `00:16:24Z`. Focal and audit both exited
zero. All eight audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9029752304`, named
`cmp89-displayed-integrand-periodicity-747e7c6d892ed7c6bbabb0488ca3bfd87c101af0`,
has GitHub digest
`87d9be0753970c094fd48fd670c7dbf61702aefa9cb465311aa099c83ad00e4d`.
The deterministic inner archive re-hashed on Windows to
`bf41ece13bc0b6bb0b514455be85f376d32dd9bd2a25216082d615572be52665`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed brick constructs the bare numerator as a literal function of one
already-aliased momentum and derives its period from integer endpoint data,
the lattice phase identity, the fine-difference period and the average
period. The displayed finite sum is transported by the centered alias
permutation. Fine-denominator nonvanishing at the shifted endpoint is then
derived through that same permutation, while unit and reduced nonvanishing
transport through their sealed periods.

The stabilized extension is not postulated periodic globally. Its equality
is obtained only by moving stabilized-to-displayed at the shifted endpoint,
using displayed periodicity, and moving displayed-to-stabilized at the
original endpoint. Thus the theorem has exactly the original non-singular
domain hypotheses and no duplicate shifted-domain input.

Contour integration, the actual strip bound `B0`, the Fourier/physical-rate
dictionary and window-15 attainment remain open. This brick produces no
terminal field: counters remain `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

Cached diagnostic run `31285019174` passed before the cold seal. Failed run
`31284890631` preserves one elaborational repair: the bare-momentum
definition had to be unfolded symmetrically before rewriting its four
factors. No statement, domain hypothesis, period or physical object changed.

### Step 7.5br boundary-seam holomorphic vertical shift (SEALED infrastructure; physical seam and holomorphy open)

Exact source checkpoint `2e1df044b6210ca418a0132ffe62216e46f75157`
passed cold GitHub Actions run
[`31286165205`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31286165205)
with workflow checkpoint `95acf4d9094aae99753358d9368abb4c6fa7a42a`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `00:28:27Z` to `00:28:34Z`, completed
2,744 jobs, and the audit ended at `00:28:38Z`. Focal and audit both exited
zero. The audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9029897994`, named
`holomorphic-boundary-vertical-shift-2e1df044b6210ca418a0132ffe62216e46f75157`,
has GitHub digest
`6ecaa748663b6252d337e3b62bd27d96408d95e386d35c274acfd724a3fcf63d`.
The deterministic inner archive re-hashed on Windows to
`4565d20d7617880412aa4d0d547b279ab5b5bee38a37bbcb0292a65e7afc3ae9`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed theorem weakens the generic rectangular Cauchy input from global
periodicity to the pointwise equality of the two vertical boundary edges on
the actual rectangle. This is the exact seam consumed by cancellation of the
vertical integrals. It therefore permits the stabilized CMP89 continuation to
remain the holomorphic interior object while proving boundary equality only
at `p_nu = -pi` and `p_nu = pi`, where the printed non-singular dictionary is
available. No global stabilized periodicity or equality of contour integrals
is accepted as an input.

The physical boundary seam, common-strip holomorphy of the stabilized
integrand, iteration over four coordinates, `B0`, the physical-rate
dictionary and window-15 attainment remain open. This is contour
infrastructure, not a terminal producer: counters remain `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31286075555` passed first. No failed compiler run was
required for this brick.

### Step 7.5bs stabilized-integrand conditional holomorphy (SEALED; common-strip nonzeros open)

Exact source checkpoint `379d08c86ee7c59ba7cc0a040ea222a0053252be`
passed cold GitHub Actions run
[`31286905528`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31286905528)
with workflow checkpoint `97890ca8d309f09f2d82dd7fd8acc86e8621bb6f`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `00:48:56Z` to `01:06:30Z`, completed
8,443 jobs, and the audit ended at `01:06:39Z`. Focal and audit both exited
zero. All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9030334011`, named
`cmp89-stabilized-integrand-holomorphy-379d08c86ee7c59ba7cc0a040ea222a0053252be`,
has GitHub digest
`0a3d268296cc4b5e251cbc0a39e52117601783d7fa52adc6582d04933eb4b658`.
The deterministic inner archive re-hashed on Windows to
`dcf11ae841646d4c044bdf9f4b7e2d9e1f94356eb927fdc2d0979cf49e96aca1`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed brick proves that the alias translation, endpoint phase and bare
numerator are entire, and derives pointwise differentiability of the literal
stabilized numerator, stabilized denominator and complete stabilized
integrand. Its domain contains exactly the denominator families that survive
the algebraic cancellation: noncentral fine symbols and the stabilized
denominator. It does not reintroduce nonvanishing of the unit symbol, reduced
denominator or central fine symbol.

Producing those two surviving nonzero families uniformly from the already
sealed common scalar radius remains the next brick. The physical boundary
seam, iterated contour displacement, `B0`, the physical-rate dictionary and
window-15 attainment remain open. This is analytic infrastructure, not a
terminal producer: counters remain `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

Cached diagnostic run `31286813485` passed first. Failed runs `31286438596`,
`31286581972` and `31286703329` record only elaborational repairs: explicit
Fréchet inversion replaced an ambiguous one-dimensional quotient derivative,
and the already proved entire average amplitude was registered locally for
`fun_prop`. No statement, denominator family, hypothesis or constant changed.

### Step 7.5bt common-strip stabilized holomorphy (SEALED; physical boundary seam open)

Exact source checkpoint `44e68aee0ec5910738068ee4188a6bbbfd00e4bd`
passed cold GitHub Actions run
[`31287808567`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31287808567)
with workflow checkpoint `07dce14e3401bd3f2e156c79bb8ad63534fb7df3`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `01:14:34Z` to `01:30:41Z`, completed
8,444 jobs, and the audit ended at `01:30:49Z`. Focal and audit both exited
zero. All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9030582290`, named
`cmp89-common-strip-holomorphy-44e68aee0ec5910738068ee4188a6bbbfd00e4bd`,
has GitHub digest
`96ec9b4de34465ddae16f6fe1a1c6f1c327c225a8f9ea6ddc5e8648978a1a838`.
The deterministic inner archive re-hashed on Windows to
`a1dd47599a50e82854e387b48f350357568b8ce2ada5f1c282528f22d68b16cb`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed producer consumes the one common positive scalar radius already
constructed for the amplitude, noncentral-gap and stabilized-denominator
budgets. It derives nonvanishing of every literal noncentral fine symbol,
derives stabilized-denominator nonvanishing, and feeds exactly those two
families to the conditional holomorphy theorem. Unit-symbol,
reduced-denominator and central-fine-symbol nonvanishing are not reintroduced.
The flowing inputs `0 < mass` and `mass^2 <= 1` remain explicit.

Thus the stabilized integrand is now holomorphic throughout one common
positive strip by a single compiled witness, rather than by three separately
compatible radii. The next brick must derive the boundary seam on the two
Brillouin faces; after that, the generic boundary-seam Cauchy theorem can be
specialized coordinatewise. No contour equality, complete bound `B0`,
physical-rate dictionary, window-15 attainment or terminal field is produced.
Counters remain `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.

Cached diagnostic run `31287705245` passed first. The source compiled on its
first execution; no failed Lean run or post-checkpoint change was required.

### Step 7.5bu physical stabilized boundary seam (SEALED; contour displacement open)

Exact source checkpoint `c41125577a863b56297ea65e44d247df818ada51`
passed cold GitHub Actions run
[`31288836441`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31288836441)
with workflow checkpoint `a75893c501e00d875ccd91b81c794a7c77c770cf`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `01:44:42Z` to `02:01:58Z`, completed
8,455 jobs, and the audit ended at `02:02:05Z`. Focal and audit both exited
zero. All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9030920516`, named
`cmp89-stabilized-boundary-seam-c41125577a863b56297ea65e44d247df818ada51`,
has GitHub digest
`66f34ab062969f639d236b2069e5cd681713c56800c767002048b98ff39ff582`.
The deterministic inner archive re-hashed on Windows to
`f3efe7918f45e44949fc9c3e1edfd857c1722c8e3838dd9f02b6d66ee4d5111c`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

On the lower Brillouin face the sealed producer constructs every
non-singularity required by the original displayed rational integrand. The
zero alias obtains its fine-symbol gap from the boundary coordinate; nonzero
aliases use the sealed radial gap. The reduced denominator is recovered from
the exact central-fine-times-reduced stabilization identity. Only after this
literal displayed domain is built does the proof transport the already
sealed physical period to the stabilized extension. No global stabilized
periodicity is postulated.

This is the vertical-face seam consumed by the generic boundary-seam Cauchy
theorem, not yet its coordinatewise specialization. Iterated contour
displacement, the complete strip bound `B0`, the Fourier/physical-rate
dictionary, window-15 attainment and every terminal field remain open.
Counters remain `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.

Cached diagnostic run `31288719986` passed first. Failed diagnostic run
`31288609402` records only the explicit pinning of `L`, `j`, `mass`, `a` and
`rho` at the physical endpoint; no statement, hypothesis, denominator family
or scalar constant changed.

### Step 7.5bv one-coordinate physical contour shift (SEALED; four-coordinate iteration open)

Exact source checkpoint `0ec0a3f4e5dbd1491ed48c60f00cae6418d485da`
passed cold GitHub Actions run
[`31290450731`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31290450731)
with workflow checkpoint `e7443a2e9a72ac889c1246f7beb04ba4ccd8eb8b`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `02:31:40Z` to `02:49:46Z`, completed
8,458 jobs, and the audit ended at `02:49:53Z`. Focal and audit both exited
zero. All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9031420870`, named
`cmp89-one-coordinate-contour-shift-0ec0a3f4e5dbd1491ed48c60f00cae6418d485da`,
has GitHub digest
`e6f7242c5a25a5d98ad03a37073e98a9bf5bb381dab114daf255f1bb90b0c6c4`.
The deterministic inner archive re-hashed on Windows to
`83e857ed718464b3d16629e85e7d799b4f4f5ecbac713847ebef607bfbccca04`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed theorem translates one physical coordinate from `[-pi,pi]` to a
line of length `2*pi`, constructs holomorphy of that line throughout the
rectangle from the common strip, supplies the two vertical-edge equality
from the physical seam, and applies the generic boundary-seam Cauchy theorem.
The coordinate is real before it is shifted; previously shifted coordinates
may already carry imaginary parts bounded by the same `rho`. No global
periodicity premise is used.

This proves one coordinate integral equality only. Iteration over all four
coordinates, the complete strip bound `B0`, the Fourier/physical-rate
dictionary, window-15 attainment and every terminal field remain open.
Counters remain `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.

Cached diagnostic run `31290333906` passed first. Failed diagnostic runs
`31289762263`, `31289924013`, `31290057994` and `31290196349` record only
namespace qualification, pinned physical parameters, the explicit
single-coordinate derivative and orientation of the named seam through the
integrand. They changed no statement, hypothesis, radius or scalar constant.

### Step 7.5bw interval-integral slice transport (SEALED; endpoint split and four-coordinate iteration open)

Exact source checkpoint `3f434e990cdb8a0b985bf1d4cb91a999e53eb536`
passed cold GitHub Actions run
[`31291655520`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31291655520)
with workflow checkpoint `0cb9044b4cbcc47ac2a4050a69ca6edc1c932551`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `03:05:41Z` to `03:05:44Z`, and the
audit ended at `03:05:48Z`. Both stages exited zero. The single audited
declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9031601546`, named
`interval-integral-slice-transport-3f434e990cdb8a0b985bf1d4cb91a999e53eb536`,
has GitHub digest
`1d258368e31064996dcc76c875bf76acd723f81560b95ee883bb32a3bce77983`.
The deterministic inner archive re-hashed on Windows to
`8d9138f1ea83b61e033746e9b0af9a5f1ac239199fbcc1028e21ab7419538328`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed theorem lifts equality of one-coordinate interval integrals on
every remaining slice to equality of the full iterated integrals. Integrability
of both uncurried functions against the restricted interval product measure
is explicit and load-bearing; this is Fubini transport, not formal
congruence.

This brick does not justify shifting the unsplit physical phase difference.
The holder-plus-transport and transport-only endpoints must first be split
algebraically and then shifted with their own sign vectors. Endpoint-specific
holomorphy and seams, four-coordinate iteration, the complete bound `B0`, the
physical owner dictionary, window-15 attainment and every terminal field
remain open. Counters stay `20/41`, `TermSource = 0`, and window 15 compatible
but unattained.

Cached diagnostic run `31291537945` passed first but did not retire
PRE-VALIDATION. Only the cold run above did.

### Step 7.5bx stabilized endpoint split (SEALED; endpoint contour shifts open)

Exact source checkpoint `e288842456b9a39e148eae4459620edb5abc5eb1`
passed cold GitHub Actions run
[`31292068036`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31292068036)
with workflow checkpoint `edcba146f378d1bfda02d5d0e144c2c01b511adb`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `03:17:34Z` to `03:34:42Z`, completed
8,444 jobs, and the audit ended at `03:34:49Z`. Both stages exited zero. All
six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9031912782`, named
`stabilized-endpoint-split-e288842456b9a39e148eae4459620edb5abc5eb1`,
has GitHub digest
`7386a0e210e0f4472521993c0738a5c2f945cd88225c728ac0f6df3559342604`.
The deterministic inner archive re-hashed on Windows to
`73dbcd0f3b1dbca487d89c8980fa97a1c9f3d136656e56dfeb968734ed183faf`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed construction does not accept endpoint functions. It rebuilds each
endpoint from the literal zero-alias branch, noncentral fine-symbol quotients
and common stabilized denominator, then proves exact subtraction identities
at the bare-alias, assembled-numerator and complete-integrand levels. Thus the
holder-plus-transport and transport-only phases can receive distinct signed
contours without pretending that one shift controls their difference.

No endpoint holomorphy, endpoint seam, contour displacement, `B0`, owner
dictionary, window-15 attainment or terminal field is produced. Counters stay
`20/41`, `TermSource = 0`, and window 15 compatible but unattained.

Cached diagnostic run `31291955125` passed on the first source and did not
retire PRE-VALIDATION. Only the cold run above did.

### Step 7.5by stabilized endpoint holomorphy (SEALED; endpoint seams open)

Exact source checkpoint `de63c0d0266cb6969363e4c478252d93d5e56b79`
passed cold GitHub Actions run
[`31292952123`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31292952123)
with workflow checkpoint `c358a06717318ce98763e6efbc15f2b01b5bf78f`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `03:43:14Z` to `04:00:12Z`, completed
8,447 jobs, and the audit ended at `04:00:20Z`. Both stages exited zero. All
four audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9032221129`, named
`stabilized-endpoint-holomorphy-de63c0d0266cb6969363e4c478252d93d5e56b79`,
has GitHub digest
`f312b42475aa18f23badbf1d193f455f1901d32047f3876387d074205bdd8f1d`.
The deterministic inner archive re-hashed on Windows to
`ff59d50b65fd173998f22ac0c4bcb7415aa1a3df9bd37923e772f403946373be`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

Each constructed endpoint numerator is now entire before the literal
noncentral fine-symbol divisions. The assembled numerator and complete
endpoint integrand are differentiable wherever exactly those fine symbols
and the common stabilized denominator are nonzero. The sealed common-radius
producer discharges those same two families; no radius, mass condition or
denominator hypothesis was added.

Endpoint seams and contour shifts, compact-product integrability, `B0`, the
owner dictionary, window-15 attainment and every terminal field remain open.
Counters stay `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.

Cached diagnostic run `31292852815` passed on the first source and did not
retire PRE-VALIDATION. Only the cold run above did.

### Step 7.5bz stabilized endpoint periodicity (SEALED; endpoint boundary seam open)

Exact source checkpoint `0550a2164c6cfd63b54cbd7e010f5c49f8fcc15e`
passed cold GitHub Actions run
[`31293915861`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31293915861)
with workflow checkpoint `7bf166179d321c7fa4f99908c07ddf02139df58b`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `04:09:46Z` to `04:26:37Z`, completed
8,457 jobs, and the audit ended at `04:26:46Z`. Both stages exited zero. All
twelve audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9032506305`, named
`stabilized-endpoint-periodicity-0550a2164c6cfd63b54cbd7e010f5c49f8fcc15e`,
has GitHub digest
`6eac46a4aaae32f479bb32d3685cc0de56cfcf38c59271ca873cbeeb8ec8f67a`.
The deterministic inner archive re-hashed on Windows to
`58f946e93a9859767dd5711c7dd616cc413a1a69a08837a4ef45558ea73ea0bd`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed route constructs each displayed endpoint alias term and finite
sum, proves its physical period by the exact centered-alias permutation, and
then transfers that period to the stabilized endpoint only where the unit,
reduced and full fine-symbol domain is available. Shifted non-singularity is
derived internally. No global stabilized-endpoint period is postulated.

The Brillouin-face producer and endpoint seam, contour displacement, compact
product integrability, `B0`, owner dictionary, window-15 attainment and every
terminal field remain open. Counters stay `20/41`, `TermSource = 0`, and
window 15 compatible but unattained.

Cached diagnostic run `31293818233` passed on the first source and did not
retire PRE-VALIDATION. Only the cold run above did. The cold focal emitted no
warning from the new endpoint-periodicity module; inherited linter warnings
come from pre-existing dependencies.

### Step 7.5ca stabilized endpoint boundary seam (SEALED; endpoint contour shift open)

Exact source checkpoint `bb7ee9ac4e18691e2257b885f56f588b472833bc`
passed cold GitHub Actions run
[`31294828439`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31294828439)
with workflow checkpoint `89964e4b22984c695f5c533c23128902c646d881`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `04:35:53Z` to `04:48:23Z`, completed
8,459 jobs, and the audit ended at `04:48:27Z`. Both stages exited zero. The
audited declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9032754393`, named
`stabilized-endpoint-boundary-seam-bb7ee9ac4e18691e2257b885f56f588b472833bc`,
has GitHub digest
`3545b46facd28e6ecfe1fdb40a5876c0c1058e1d30d6e252e22afa353bd0d0bf`.
The deterministic inner archive re-hashed on Windows to
`0049aa824b429309ee2b28aa38ddc860f322b513ff8926c075715d1868e56f89`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed theorem first constructs the full displayed non-singular domain
on the lower Brillouin face and then consumes the endpoint physical period.
It introduces no global periodicity premise and no new scalar condition.

The endpoint contour equality, compact-product integrability, four-coordinate
iteration, `B0`, owner dictionary, window-15 attainment and every terminal
field remain open. Counters stay `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

Cached diagnostic run `31294728096` passed on the first source and did not
retire PRE-VALIDATION. Only the cold run above did.

### Step 7.5cb one-coordinate stabilized endpoint shift (SEALED; four-coordinate iteration open)

Exact source checkpoint `712ffb674296a59e940adf607672fed89d5f5463`
passed cold GitHub Actions run
[`31295576434`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31295576434)
with workflow checkpoint `0101d180f6bc4af5e84ca494c61eea4ae7de3dad`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `04:56:55Z` to `05:14:44Z`, completed
8,463 jobs, and the audit ended at `05:14:50Z`. Both stages exited zero. The
audited declaration uses exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9033029246`, named
`stabilized-endpoint-one-coordinate-shift-712ffb674296a59e940adf607672fed89d5f5463`,
has GitHub digest
`6b8eadfeb747ee73bef6d42b94b1185e724dda337b5586833d1553e7eaa5a5ca`.
The deterministic inner archive re-hashed on Windows to
`b7eaa6f3ec94d37fc09a01ba0c4a66cd073cc3d63b192f5b28278ee1fcd35447`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed theorem specializes the rectangular Cauchy route to one literal
constructed endpoint integrand. Common-strip holomorphy and the physical
endpoint seam are derived internally; no global endpoint periodicity,
endpoint family, or contour equality is accepted as input.

Compact-product integrability, transport over the remaining coordinates,
four-coordinate iteration, recombination of the two endpoint contours,
`B0`, the owner dictionary, window-15 attainment and every terminal field
remain open. Counters stay `20/41`, `TermSource = 0`, and window 15 compatible
but unattained. Cached diagnostic run `31295482971` did not retire
PRE-VALIDATION; only the cold run above did.

### Step 7.5cc finite-product coordinate transport (SEALED; physical iteration open)

Exact source checkpoint `80c13cb97eee0fe918042ad310b73dbeebcd23a6`
passed cold GitHub Actions run
[`31296564841`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31296564841)
with workflow checkpoint `575e375511e02e3bd2f88078b6db773520b60a96`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `05:24:54Z` to `05:25:00Z`, completed
2,591 jobs, and the audit ended at `05:25:05Z`. Both stages exited zero. Both
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9033140110`, named
`pi-coordinate-interval-transport-80c13cb97eee0fe918042ad310b73dbeebcd23a6`,
has GitHub digest
`b42a2fe43191fee5b919a098a5d161fa754d9c860728f930bcffd0492b9a05c7`.
The deterministic inner archive re-hashed on Windows to
`1b8428162b71e3c39c977adb3635c40b04c75e0073358326b7cc8133b175690e`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed route lifts a slice equality that holds almost everywhere in the
remaining coordinates through a finite product integral. It uses the exact
`piFinSuccAbove` measure equivalence and explicit integrability of both
uncurried functions. It does not strengthen a Brillouin-domain identity to
points outside the restricted cube.

Physical compact-product integrability, endpoint-specific four-coordinate
iteration, endpoint recombination, `B0`, the owner dictionary, window-15
attainment and every terminal field remain open. Counters stay `20/41`,
`TermSource = 0`, and window 15 compatible but unattained. Cached diagnostic
run `31296472882` did not retire PRE-VALIDATION; only the cold run above did.

### Step 7.5cd stabilized endpoint product integrability (SEALED; four-coordinate iteration open)

Exact source checkpoint `6d1eaa990586310a13e8249a32f0d496c80dd2f8`
passed cold GitHub Actions run
[`31297566862`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31297566862)
with workflow checkpoint `96b2d09b4df216c50ba1757f6667d7beeb04ad49`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `05:52:35Z` to `06:04:39Z`, completed
8,466 jobs, and the audit ended at `06:04:46Z`. Both stages exited zero. All
nine audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9033597974`, named
`stabilized-endpoint-product-integrability-6d1eaa990586310a13e8249a32f0d496c80dd2f8`,
has GitHub digest
`4f07cbddc232f49314cb1c5bacafe364d42678d2a09f447bed0ef79e8683c68b`.
The deterministic inner archive re-hashed on Windows to
`3773dbf3c148e803c052a414c41cf9378e18a6e8fd25f0b81a35491486f33934`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed theorem constructs every partial signed endpoint momentum and
derives compact-product integrability from common-strip physical holomorphy.
It does not accept a family of endpoint functions or an integrability premise.
The literal signed `l1` decay and its exact product sum are already sealed in
`BalabanCMP89SignedLatticeL1ExponentialSum`; the later `B0` route must retain
that `delta^(-d)` geometry rather than reintroduce the ball-counting
`delta^(-(d+1))` majorant.

Four-coordinate iteration, endpoint recombination, the complete strip bound
`B0`, the owner-to-lattice dictionary, window-15 attainment and every terminal
field remain open. Counters stay `20/41`, `TermSource = 0`, and window 15
compatible but unattained. Cached diagnostic run `31297455930` did not retire
PRE-VALIDATION; only the cold run above did.

### Step 7.5ce stabilized endpoint product coordinate step (SEALED; four-step telescope open)

Exact source checkpoint `6c3698f1749419fed4d91c8f6b443cd96dd58f4f`
passed cold GitHub Actions run
[`31298945808`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31298945808)
with workflow checkpoint `fcddf7155e3483a57b8fb6d4926a60bfec23cef4`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `06:30:00Z` to `06:48:29Z`, completed
8,467 jobs, and the audit ended at `06:48:39Z`. Both stages exited zero. All
five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9034108517`, named
`stabilized-endpoint-product-coordinate-shift-6c3698f1749419fed4d91c8f6b443cd96dd58f4f`,
has GitHub digest
`fe53f789a0a5e90dd55e3a0d8193edc514967f7e053c1b3a0a4ff5757f720cb0`.
The deterministic inner archive re-hashed on Windows to
`68310ad06b92979eabf31f5c3b78fc5c8aebc81a713e2b356075badf558db886`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed theorem transports the literal four-dimensional product integral
from partial signed stage `r` to `r+1`. It derives both product-integrability
premises internally, decomposes the finite Pi measure at the selected
coordinate, and invokes the sealed endpoint contour theorem on almost every
remaining slice. Its strip premise is the full-polydisc condition
`forall mu, |Im (z mu)| <= rho`; hence already-shifted coordinates remain
inside the certified domain at later stages. It neither assumes a family of
slice equalities nor weakens the other coordinates back to the real slice.

The finite telescope through stages `0,1,2,3,4` is still open. Endpoint
recombination must remain a separate brick: the two endpoint terms use
different signed contours. The later single-owner decay must cite the lattice
fact that the two physical endpoints are neighbours and pay the literal
factor `exp rho`; that cost must not be absorbed into an anonymous `B0`.
The complete bound `B0`, owner dictionary, window-15 attainment and every
terminal field remain open. Counters stay `20/41`, `TermSource = 0`, and
window 15 compatible but unattained. Cached diagnostic run `31298811187`
did not retire PRE-VALIDATION; only the cold run above did.

### Step 7.5cf stabilized endpoint four-coordinate telescope (SEALED; endpoint recombination open)

Exact source checkpoint `8a4f1b3a05abf165d75b2a22359c46ecc7f72119`
passed cold GitHub Actions run
[`31300130079`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31300130079)
with workflow checkpoint `864cc4121917dca4a44fa9d1e2402d5c92759be2`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `07:02:02Z` to `07:15:30Z`, completed
8,468 jobs, and the audit ended at `07:15:37Z`. Both stages exited zero. Both
audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9034397683`, named
`stabilized-endpoint-product-contour-telescope-8a4f1b3a05abf165d75b2a22359c46ecc7f72119`,
has GitHub digest
`ff5aedcf9814b7c1a74304341ca94a0a43164695c570d7fc2261fec5073efc19`.
The deterministic inner archive re-hashed on Windows to
`5b6de45e886e40519004342cd00cd29a3a3d724364f4f77c6983637fdaa0b0f4`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed telescope composes the literal stages `0 -> 1 -> 2 -> 3 -> 4`
for one endpoint and rewrites stage zero to the real Brillouin momentum and
stage four to that endpoint's fully signed momentum. Every intermediate stage
uses the already-sealed full-polydisc strip condition, so no single-coordinate
nonvanishing premise is smuggled into the iteration.

This does not shift the difference of the two endpoint terms on one common
contour. Endpoint recombination remains separate and must cite that the two
physical endpoints differ by one lattice edge, yielding the explicit factor
`exp rho` when their `l1` decays are compared. The complete bound `B0`, owner
dictionary, window-15 attainment and every terminal field remain open.
Counters stay `20/41`, `TermSource = 0`, and window 15 compatible but
unattained. Cached diagnostic run `31300025712` did not retire
PRE-VALIDATION; only the cold run above did.

### Step 7.5cg stabilized endpoint recombination (SEALED; physical owner dictionary and `B0` open)

Exact source checkpoint `b47f419570f33419bfefb49f8da9a78b52aac09c`
passed cold GitHub Actions run
[`31301585184`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31301585184)
with workflow checkpoint `6c1ac2e58d641811a8431985827019ccd0736274`.
The job recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `07:39:15Z` to `07:56:46Z`, completed
8,469 jobs, and the audit ended at `07:56:55Z`. Both stages exited zero. All
six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9034863784`, named
`stabilized-endpoint-recombination-b47f419570f33419bfefb49f8da9a78b52aac09c`,
has GitHub digest
`91cb0f7ffe8ac08b6e2791e75b002a7c25b6756fb38b82a768758260b03c637e`.
The deterministic inner archive re-hashed on Windows to
`99b50c6f9658156a7e3e8cea218c4bcdefb50c19243f1aca2bfffa7ad025b89c`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The complete real stabilized product integral is now exactly the difference
of the two endpoint integrals shifted along their own signed four-coordinate
contours. No common contour or endpoint-bound family is accepted. The same
brick names the literal unit-edge condition
`CMP89Eq251UnitLatticeBondDisplacement` and proves that it transports the
second `l1` decay to the first with the explicit multiplicative cost
`exp rho`.

The current Fourier endpoint variables are still arbitrary integer lattice
displacements. Consequently the unit-edge condition is not silently attached
to the abstract telescope: the physical owner/bond dictionary must construct
it from the two endpoints of one lattice link. The two endpoint magnitude
bounds, their complete `B0`, Fourier-to-owner transport, window-15 attainment
and all terminal fields remain open. Counters stay exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained. Cached diagnostic
run `31301472527` did not retire PRE-VALIDATION; only the cold run above did.

### Step 7.5ch unit-lattice Holder normalization (SEALED; physical owner dictionary and `B0` open)

Exact source checkpoint `aa1275df13a40733af754b92bc947a8e82c0a727`
passed cold GitHub Actions run
[`31303591996`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31303591996)
with workflow checkpoint `77344497dc96302a5ffb781167fc57e6d82503ef`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `08:29:53Z` to `08:47:26Z`, completed
8,471 jobs, and the audit ended at `08:47:32Z`. Both stages exited zero. All
five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9035463194`, named
`unit-lattice-holder-normalization-aa1275df13a40733af754b92bc947a8e82c0a727`,
has GitHub digest
`d6435a3b0cb411bdf20f7d9b19134f34ee7557864069a58edf90e5e19b58e963`.
The deterministic inner archive re-hashed on Windows to
`3e09ddbe979c97040554d995dbae482250bb075f538042a0f417e50b68376575`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The named unit-edge lattice premise now derives internally the exact real
`l1` length one, Euclidean momentum square one, Euclidean norm one and hence
every real Holder power equal to one. No lower norm bound or normalization
factor survives as a separate input. This removes an artificial analytic
premise from the later endpoint estimate, but does not construct the physical
owner-to-lattice map: that dictionary must still prove that the two endpoints
of the physical link produce `CMP89Eq251UnitLatticeBondDisplacement`.

The endpoint magnitude bounds, their complete scale-uniform `B0`,
Fourier-to-owner transport, window-15 attainment and all terminal fields
remain open. Counters stay exactly `20/41`, `TermSource = 0`, and window 15
compatible but unattained. Diagnostic run `31303486729` was not used to
retire PRE-VALIDATION; only the cold run above was.

### Step 7.5ci physical-bond displacement dictionary (SEALED; fine-to-owner transport and `B0` open)

Exact source checkpoint `2e295053fab0f5efa9b8e0a7521f6897e104e3b2`
passed cold GitHub Actions run
[`31305272865`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31305272865)
with workflow checkpoint `a57b874de9782ace7665f97b09facf579b02b85e`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `09:12:17Z` to `09:30:31Z`, completed
8,472 jobs, and the audit ended at `09:30:37Z`. Both stages exited zero. The
six audited declarations use only the allowed set
`[propext, Classical.choice, Quot.sound]`; two projection theorems use the
strict subset `[propext, Quot.sound]`, and the coordinatewise signed-edge
theorem uses `[propext]`.

Downloaded artifact `9035975983`, named
`physical-bond-displacement-dictionary-2e295053fab0f5efa9b8e0a7521f6897e104e3b2`,
has GitHub digest
`3db734079142da82d9d6dfa1dbd52c4aa7872af75fe0f3eb89c0d888ed3f253d`.
The deterministic inner archive re-hashed on Windows to
`6019e5ee5d9504aa6d7b6063c60a4bb950981cb316cb1c45a447dede1953a109`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The dictionary now constructs seam-safe integer lifts of the literal CMP116
physical source and target endpoints. Both lifts project back to their
periodic endpoints; subtracting source minus target gives exactly `-e_dir`,
including across the periodic seam. Hence every physical bond internally
produces `CMP89Eq251UnitLatticeBondDisplacement`, real `l1` norm one, and the
already sealed Euclidean/Holder normalization for every real exponent. The
sign is retained because the CMP89 endpoint phase consumes it.

This seals the physical-link part of the owner/bond dictionary, not the full
owner dictionary. The CMP99 localization owner is a coarse block in
`FinBox 4 (2*(K*Q))`, whereas the endpoint is a fine site. A faithful bridge
must first construct the fine-site displacement `target - y`; only afterwards
may `blockSite` compare the two fine sites through their coarse owners. A
direct subtraction `target - owner` would mix units and is not the intended
dictionary. Endpoint magnitude bounds, scale-uniform `B0`, Fourier-to-owner
transport, window-15 attainment and all terminal fields remain open. Counters
stay exactly `20/41`, `TermSource = 0`, and window 15 compatible but
unattained. Diagnostic run `31305147602` did not retire PRE-VALIDATION; only
the cold run above did.

### Step 7.5cii fine-site endpoint transport dictionary (SEALED; fine-to-owner metric bridge and `B0` open)

Exact source checkpoint `b98845a20c2b3869a9e656d28ca8a8f21a26ea63`
passed cold GitHub Actions run
[`31306842747`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31306842747)
with workflow checkpoint `d12f8d26f1413e48367aa260d82fdbc4d3fe7a1b`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal ran from `09:51:49Z` to `10:05:47Z`, completed 8,473
jobs, and the audit ended at `10:05:53Z`. Both stages exited zero. Five of the
eight audited declarations use `[propext, Quot.sound]`; the three finite-sum
bounds use the allowed standard triple
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9036387589`, named
`physical-site-transport-dictionary-b98845a20c2b3869a9e656d28ca8a8f21a26ea63`,
has GitHub digest
`bd16e6884915cfa9db901cf112a1d28dd2625a0441a6564234cc1f9e35a55988`.
The deterministic inner archive re-hashed on Windows to
`e2d5efbc9988d72ae78d63d45d1c75355f283646607424f3ba8d037411d5eba9`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The dictionary now constructs the shortest signed periodic representative of
the literal fine-site displacement `target - y`. It proves its exact `ZMod`
projection and that its real `l1` length is the sum of the four coordinatewise
torus distances, hence at most four times the literal fine Chebyshev distance.
The first endpoint is defined by the exact integer identity
`holder + transport`; its periodic projection is `source - y`, including at
the seam, and its length costs at most the already sealed single edge.
Centered representatives are deliberately not added as though they preserved
integer addition.

This is the fine-lattice half of the transport dictionary. The remaining
metric step must use `blockSite` and prove the scale-aware inverse inequality
`scale * ownerDist <= transportL1 + 2*(scale-1)` (or a sharper cited form),
with units visible. It must not subtract a coarse owner from a fine endpoint.
The complete endpoint bound `B0`, window-15 attainment and all terminal fields
remain open. Counters stay exactly `20/41`, `TermSource = 0`, and window 15
compatible but unattained. Diagnostic run `31306685086` did not retire
PRE-VALIDATION; only the cold run above did.

### Step 7.5ciii fine-to-localization-owner distance bridge (SEALED; exponential transport and `B0` open)

Exact source checkpoint `fcec88e8a0a89ed32332c7f1c6bcc76fb3bfb61d`
passed cold GitHub Actions run
[`31308045458`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31308045458)
with workflow checkpoint `f9e490578a9639f2a637f8c161c42e5520441bee`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal ran from `10:21:01Z` to `10:47:36Z`, completed 8,590
jobs, and the audit ended at `10:47:42Z`. Both stages exited zero. All six
audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9036860542`, named
`source-owner-distance-bridge-fcec88e8a0a89ed32332c7f1c6bcc76fb3bfb61d`,
has GitHub digest
`7b5510f6d267fa83f4bd2aeacc2dd5e83b652da4d35cf1017dd9655d02a413f7`.
The deterministic inner archive re-hashed on Windows to
`338a53f61ea9355eb64c6925c20a18dbfa9604e75b23048df67056cd4cd5737a`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The generic metric theorem now proves, for block side `ell`,
`ell * ownerDist <= fineDist + 2*(ell-1)` from the exact distance between
lower block corners and the two same-block boundary estimates. It is
specialized through the literal `Equiv.cast` carrier and the named CMP99
source-localization owner. A second sealed theorem proves
`fineDist <= transportL1` for the CMP89 signed displacement and composes both
facts without subtracting objects in different units.

This closes the metric conversion, not the analytic endpoint bound. The next
brick must exponentiate the inequality with signs checked in the decreasing
exponential, producing the owner rate `rho*ell` and retaining the boundary
factor `exp(2*rho*(ell-1))`. It must then be combined with the separate
single-edge factor `exp rho`; neither factor may be absorbed prematurely into
an unnamed constant. `B0`, window-15 attainment and all terminal fields remain
open. Counters stay exactly `20/41`, `TermSource = 0`, and window 15 compatible
but unattained. Diagnostic run `31307905304` did not retire PRE-VALIDATION;
only the cold run above did.

### Step 7.5civ physical endpoint exponential transport to localization owners (SEALED; endpoint amplitudes and `B0` open)

Exact source checkpoint `993f3a465244ebc7a7c64b44e5ee260ff26e0b21`
passed cold GitHub Actions run
[`31309588643`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31309588643)
with workflow checkpoint `cc8642603c07c52884d2c42fda5694df8b35c7e0`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal ran from `10:59:14Z` to `11:27:54Z`, completed 8,591
jobs and exited zero. The audit ended at `11:28:00Z` and also exited zero. All
five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9037332025`, named
`physical-owner-exponential-transport-993f3a465244ebc7a7c64b44e5ee260ff26e0b21`,
has GitHub digest
`f9ad9bbd16c59034519e671da91ec36c06bf527c751f0f9b8a755cbc3bc7d528`.
The deterministic inner archive re-hashed on Windows to
`f37c9f7a85dca8b0f032ad3f65b31760953a994bfde54f6048eb723af1057a90`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed producer exponentiates the fine-to-owner metric inequality in the
decreasing direction. It preserves the literal owner decay rate
`rho * L^(depth+1)` and keeps the block-boundary cost
`exp (rho * 2 * (L^(depth+1)-1))` visible. Negating the sealed unit Holder
edge gives the reverse endpoint comparison; the two independently shifted
endpoint weights are then recombined with the separate literal factor
`1 + exp rho`. No factor is absorbed into an unnamed constant.

This closes metric-to-exponential transport only. Endpoint numerator
amplitudes, their common scale-uniform `B0`, window-15 attainment and all
terminal fields remain open. The two reported warnings were inherited from
`BalabanCMP99SourceRegionalGreenNeumann.lean` and
`BalabanCMP99SourceSeparatedLargeBlockPartition.lean`; the new target emitted
none. Counters stay exactly `20/41`, `TermSource = 0`, and window 15 compatible
but unattained. Diagnostic run `31309479791` did not retire PRE-VALIDATION;
only the cold run above did.

### Step 7.5cv endpoint strip-factor upper bounds (SEALED; numerator assembly and `B0` open)

Exact source checkpoint `aa7cf49782924c7e4372db0a68c82827fbde9cf0`
passed cold GitHub Actions run
[`31311361134`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31311361134)
with workflow checkpoint `f2f1d8b6e26320eb9aa6d1b70943cffa219f5572`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The scaled-difference focal completed 3,282 jobs from
`11:42:06Z` to `11:42:30Z`; its audit ended at `11:42:33Z`. The central
fine-symbol focal then completed 8,440 jobs from `11:42:33Z` to `11:59:06Z`;
its audit ended at `11:59:12Z`. All four stages exited zero. All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9037672861`, named
`endpoint-strip-factor-bounds-aa7cf49782924c7e4372db0a68c82827fbde9cf0`,
has GitHub digest
`ad1ba6269bd9f9ac7e7601939461f0653e1ea656c96c1a2d591cc9a3224ecd4e`.
The deterministic inner archive re-hashed on Windows to
`328de2b819a9ac4259ced835a9af4496000338d58574b23297174a490c755e98`,
identical to the cold-run hash; all 15 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The first sealed theorem bounds one entire scaled difference by the literal
sum `|z.re| + rho*exp rho`. The second producer exposes the central fine
symbol's complete-polydisc upper bound as its already sealed vertical budget
plus its real-slice bound. These are the two missing reusable factors for the
endpoint numerator; neither theorem accepts a synthetic numerator bound.

The next analytic brick must assemble the central endpoint branch and the
noncentral alias sum. The latter must use the existing redistribution at
`alpha = 0`, because one scaled difference cancels one of the two inverse
momentum powers; it must not reuse the `alpha = -1` denominator-pair constant.
Only after that assembly may the reciprocal stabilized-denominator bound form
a common `B0`. The cold logs contain inherited linter warnings from the
rebuilt graph; neither new target emitted one. Counters stay exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained. Diagnostic run
`31311238720` did not retire PRE-VALIDATION; only the cold run above did.

### Step 7.5cvi noncentral endpoint quotient (SEALED; alias sum, central branch and `B0` open)

Exact source checkpoint `94234f769b7b5cceebd27dbafe828575c82b6a8d`
passed cold GitHub Actions run
[`31312809949`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31312809949)
with workflow checkpoint `e793adb15269c291a848ebf04356129f6043f508`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,434 jobs from `12:16:57Z` to `12:33:04Z`;
the audit ended at `12:33:12Z`. Both stages exited zero. All five audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9038070788`, named
`noncentral-endpoint-quotient-94234f769b7b5cceebd27dbafe828575c82b6a8d`,
has GitHub digest
`6e2d016cf752bfaf8fe8d8317dacdd30a8a0636fe597ab14a773938a3d2ebc6b`.
The deterministic inner archive re-hashed on Windows to
`d59a93678f987fea75c6432e16e6b29588b7f88b6e2a793f93e6bc7b3b9ec740`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed pointwise producer keeps every literal factor of one noncentral
endpoint quotient. One entire scaled difference cancels one, and only one,
of the two inverse radial powers furnished by the complex fine-symbol gap.
The remaining radial power is transported by the source-weight theorem at
the exact specialization `alpha = 0`; the `alpha = -1` denominator-pair
constant is not reused.

This closes only the pointwise noncentral quotient. The finite alias sum, the
central endpoint branch, phase and Holder insertion, common numerator bound,
complete `B0`, owner transport, window-15 attainment and every terminal field
remain open. The cold focal contained inherited graph warnings; the new target
emitted none. Counters stay exactly `20/41`, `TermSource = 0`, and window 15
compatible but unattained. Diagnostic run `31312677116` did not retire
PRE-VALIDATION; only the cold run above did.

### Step 7.5cvii noncentral endpoint quotient sum (SEALED; phase factorization, central branch and `B0` open)

Exact source checkpoint `65706caceaabd5e7c1ce67dd0e4760a090119c6e`
passed cold GitHub Actions run
[`31314071695`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31314071695)
with workflow checkpoint `97c17bf70ee62497420608bca3c064948eb12cbd`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,435 jobs from `12:47:09Z` to `13:02:59Z`;
the audit ended at `13:03:06Z`. Both stages exited zero. All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9038416203`, named
`noncentral-endpoint-quotient-sum-65706caceaabd5e7c1ce67dd0e4760a090119c6e`,
has GitHub digest
`5852a6f85e8e993ded62c84ac9b0f82498149ea284020e5e7f7ffce15472a124`.
The deterministic inner archive re-hashed on Windows to
`95b8c70e30e6381f26a193fe601fbbb1b52dc815444bdae70096acc4721e4c54`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed producer sums the pointwise `alpha = 0` quotient bound over the
literal noncentral finite alias fibre and applies the exact product/tsum bound
without a fibre-cardinality factor. It proves a norm bound for the quotient
sum, not a bound for a sum of norms. Consequently the next physical endpoint
assembly must first prove that the lattice endpoint makes every alias phase
equal to the zero-alias phase and factor that common phase exactly; no
triangle-inequality substitution is permitted.

This closes the noncentral quotient sum only. Exact lattice-phase
factorization, the central endpoint branch, common numerator bound, complete
`B0`, owner transport, window-15 attainment and every terminal field remain
open. The cold focal contained inherited graph warnings; the new target
emitted none. Counters stay exactly `20/41`, `TermSource = 0`, and window 15
compatible but unattained. Failed diagnostic run `31313768608` exposed only
the cast normalization `↑(L^j)` versus `(↑L)^j`; corrected diagnostic run
`31313930119` passed but did not retire PRE-VALIDATION. Only the cold run above
did.

### Step 7.5cviii exact endpoint-amplitude factorization (SEALED; amplitude bound and `B0` open)

Exact source checkpoint `5f3d4b221bc6af5bb8fc793d0eaf11467715d594`
passed cold GitHub Actions run
[`31315566647`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31315566647)
with workflow checkpoint `9e2a84bdb04a5b1878c01f185107171cba45f31c`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,450 jobs from `13:22:33Z` to `13:39:29Z`;
the audit ended at `13:39:37Z`. Both stages exited zero. All ten audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9038858784`, named
`endpoint-amplitude-factorization-5f3d4b221bc6af5bb8fc793d0eaf11467715d594`,
has GitHub digest
`9b2df522e0437ea384f080a72b7f217f470d48fe7a1912ec4b831b093fe9b243`.
The deterministic inner archive re-hashed on Windows to
`b0840759bb8283f8b4c1b81f0feee82dea2201edcf26ebc53adf14eb0c617381`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

For an arbitrary reciprocal alias and a literal integer endpoint, the sealed
theorem computes the extra phase as the integral multiple
`2*pi*<m,u>` and removes it by exact exponential periodicity. Consequently
every noncentral branch, the full noncentral sum, the zero branch and the
complete stabilized endpoint numerator factor through one common lattice
phase. No triangle-inequality replacement of the quotient sum is used.

This closes exact phase insertion and central/noncentral assembly only. The
norm bound for the phase-free endpoint amplitude, its common scale-uniform
`B0`, the already named physical owner transport, window-15 attainment and
every terminal field remain open. The separate sealed endpoint-recombination
brick continues to supply the literal one-link factor `exp rho`; it is not
absorbed here. Counters stay exactly `20/41`, `TermSource = 0`, and window 15
compatible but unattained. Failed diagnostic runs `31315063337` and
`31315224827` exposed only reduction/order issues in the exact phase algebra;
corrected diagnostic run `31315444910` passed but did not retire
PRE-VALIDATION. Only the cold run above did.

### Step 7.5cix phase-free endpoint-amplitude bound (SEALED; complete `B0` open)

Exact source checkpoint `81768889cebfd72c4095efc0f8d9099dc15fad81`
passed cold GitHub Actions run
[`31317147898`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31317147898)
with workflow checkpoint `bc1b49b748bbe78708d25498f0a68febc52ba687`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,452 jobs from `13:58:59Z` to `14:11:01Z`;
the audit ended at `14:11:07Z`. Both stages exited zero. All four audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9039246947`, named
`endpoint-amplitude-bound-81768889cebfd72c4095efc0f8d9099dc15fad81`,
has GitHub digest
`5c8636b037b5325a2f22b3fee3ae9737c86bbf480aed0ad01cb9a2590c9b3878`.
The deterministic inner archive re-hashed on Windows to
`f8002798136ad88131431f3a0d11afdcacb66d6fd3e17ea725f20c29e3e0747d`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed bound preserves the literal central/noncentral split. The central
branch is bounded by the product of one scaled-difference strip budget and
the scale-uniform averaging-amplitude budget. The noncentral branch is the
product of the central fine-symbol budget and the already sealed norm of the
complete quotient sum. No sum-of-norms replacement, fibre cardinality or
synthetic endpoint majorant is introduced.

This closes the phase-free endpoint amplitude only. The phase weight and its
physical owner transport remain separate sealed inputs, including the
literal one-link factor `exp rho` and the block-boundary factor. Combining
those with the stabilized reciprocal to form the complete scale-uniform `B0`,
then transporting it through the remaining CMP89/CMP95/CMP96/CMP99
dictionaries, remains open. Window 15 and every terminal field remain open;
counters stay exactly `20/41`, `TermSource = 0`, and window 15 compatible but
unattained. Failed diagnostic runs `31316653059` and `31316823891` exposed
only the syntactic order of the two real summands; corrected diagnostic run
`31316997359` passed but did not retire PRE-VALIDATION. Only the cold run above
did.

### Step 7.5cx stabilized endpoint-integrand bound (SEALED; normalized integration and `B0` open)

Exact source checkpoint `e5d1e5db66a96ab5e929a3636c1afc542da410f0`
passed cold GitHub Actions run
[`31318800330`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31318800330)
with workflow checkpoint `8461574a4a9aa26304b2ca3dc7c5ac3fd63212ae`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped. The focal completed 8,478 jobs from `14:36:18Z` to `14:54:02Z`;
the audit ended at `14:54:10Z`. Both stages exited zero. All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9039784347`, named
`stabilized-endpoint-bound-e5d1e5db66a96ab5e929a3636c1afc542da410f0`,
has GitHub digest
`1d9135f8960768a39e9e59c176b304028cc8bf7d69a9226be35b097813a1bce6`.
The deterministic inner archive re-hashed on Windows to
`b7e874ecef6aab834d7a43cafe9491a7c0655e8bd4c19a599f840c4e0b4f6927`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed pointwise producer combines the exact endpoint phase
factorization, the phase-free amplitude bound and the stabilized reciprocal
bound on the endpoint's own signed contour. A literal unit Holder edge removes
the Holder normalization internally. The conclusion retains the exact signed
lattice `l1` exponential weight and the two majorant factors remain visible.

This closes the pointwise endpoint integrand only. CMP89 (2.49), visually
checked on printed page 585, carries the literal normalization `(2*pi)^(-d)`
outside the Brillouin integral. The next producer must preserve `(2*pi)^(-4)`
and cancel it against the exact volume of the translated `[0,2*pi]^4` cube;
that normalization is not part of `B0`. Integration, endpoint recombination,
the separate `exp rho` one-link cost, owner transport, complete physical `B0`,
window-15 attainment and every terminal field remain open. Counters stay
exactly `20/41`, `TermSource = 0`, and window 15 compatible but unattained.
Failed diagnostic runs `31318211467`, `31318353378` and `31318502966`
exposed only endpoint exponent normalization and unfolding issues; corrected
diagnostic run `31318648829` passed but did not retire PRE-VALIDATION. Only the
cold run above did.

### Step 7.5cxi source-normalized endpoint integration (SEALED; endpoint recombination and `B0` open)

Exact source checkpoint `a92695ec57772ba180446e3e682e0aeaaca606fc`
passed cold GitHub Actions run
[`31321423849`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31321423849)
with workflow checkpoint `321af2931e7b8bf56868e994879a39634da0b750`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped.  The exact-measure reproducer exited zero, the focal completed
8,479 jobs from `15:35:10Z` to `15:52:41Z`, and the audit ended at
`15:52:53Z`.  All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9040515330`, named
`normalized-endpoint-integral-a92695ec57772ba180446e3e682e0aeaaca606fc`,
has GitHub digest
`6bc64877bae588e53499cb91f17e2f560fd13bc4e2b40740e8ade9746a034de7`.
Its deterministic inner archive re-hashed on Windows to
`5936a94cebdc0b2325cb6286089c8e337733ad997230387cd99e19918762f14b`,
identical to the cold-run hash; all 14 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed producer defines the literal translated four-dimensional
Brillouin product measure, proves its finiteness and exact real volume
`(2*pi)^4`, and cancels that volume against the external `(2*pi)^(-4)` factor
printed in CMP89 (2.49).  A pointwise constant bound therefore loses no
normalization factor.  Specializing to one complete stabilized endpoint
retains the exact signed lattice `l1` weight and the explicit common endpoint
amplitude majorant.

This closes normalized integration for one endpoint only.  The two separately
shifted endpoints still have to be recombined; their neighbour comparison
must retain the existing literal `1 + exp rho` cost before owner transport.
The complete physical `B0`, window-15 attainment, every terminal field and
`TermSource` remain open.  Counters stay exactly `20/41`, `TermSource = 0`,
and window 15 compatible but unattained.  Failed diagnostic run
`31321096355` exposed only the final finite-ENNReal atom in the measure
reproducer; corrected diagnostic run `31321241509` passed but did not retire
PRE-VALIDATION.  Only the cold run above did.

### Step 7.5cxii normalized two-endpoint recombination (SEALED; physical owner specialization and `B0` open)

Exact source checkpoint `f5fd7a53251474932f130d817f50242c3bf67571`
passed cold GitHub Actions run
[`31322584031`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31322584031)
with workflow checkpoint `3c264eb4cd873359d32a6a042d6857ab9911e27d`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped.  The focal completed 8,480 jobs from `16:01:07Z` to
`16:19:35Z`, and the audit ended at `16:19:45Z`.  All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9040850492`, named
`normalized-stabilized-recombination-f5fd7a53251474932f130d817f50242c3bf67571`,
has GitHub digest
`2a3fea7292f79edf410ae015b8a1af69375f10f273d95d21b27c571f86ccc552`.
Its deterministic inner archive re-hashed on Windows to
`2a679630fe7f6ce12282eaff4a66559d3f95a0821909109faca6a46683c637f7`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed producer preserves the literal `(2*pi)^(-4)` normalization while
rewriting the complete stabilized integral as the difference of the two
separately shifted normalized endpoint integrals.  Its norm theorem applies
the two endpoint bounds independently and retains the literal sum of their
signed-lattice `l1` weights times the common explicit amplitude majorant.  It
does not assign a common contour sign to the two endpoints.

This seal deliberately does not absorb the later one-link factor `exp rho` or
identify the two endpoint weights with an owner decay.  The physical owner
specialization, complete scale-uniform `B0`, window-15 attainment, every
terminal field and `TermSource` remain open.  Counters stay exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.  Diagnostic run
`31322453616` passed but did not retire PRE-VALIDATION.  Only the cold run
above did.

### Step 7.5cxiii physical normalized owner bound (SEALED; owner summation and scale-uniform `B0` open)

Exact source checkpoint `1a464e4b276117ed64606ed8c6e0f113b745ef96`
passed cold GitHub Actions run
[`31323982040`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31323982040)
with workflow checkpoint `dbe9f94e7620fad40fdf606b1503feba6e1c92f9`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were skipped.  The focal completed 8,601 jobs from `16:32:36Z` to
`17:01:30Z`, and the audit ended at `17:01:37Z`.  All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9041349925`, named
`physical-normalized-owner-bound-1a464e4b276117ed64606ed8c6e0f113b745ef96`,
has GitHub digest
`54acb36a873a68e2c953d62f1e15368f86d9d41245d8d7de34fa372513765a79`.
Its deterministic inner archive re-hashed on Windows to
`88a1bd9206198b19e062e9da93f9daad09ef5e6e2225fc03cb5e827bd2cca44c`,
identical to the cold-run hash; all 13 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed producer specializes the normalized two-endpoint theorem to the
literal physical bond Holder displacement and the shortest signed
target-to-site transport.  It cites the existing owner-distance comparison
and obtains one owner decay at rate `rho * L^(depth+1)`.  Its coefficient
retains, separately and literally, the endpoint-amplitude majorant, the
one-link cost `1 + exp rho`, and the block-boundary factor
`exp (2 * rho * (L^(depth+1) - 1))`.  Nonnegativity of the explicit amplitude
majorant is derived internally from the same strip and central-window inputs.

This coefficient is scale-explicit, not yet a scale-uniform `B0`: the visible
block-boundary factor has not been eliminated or absorbed by an owner sum.
Owner summation, the complete regional Green certificate, window-15
attainment, every terminal field and `TermSource` remain open.  Counters stay
exactly `20/41`, `TermSource = 0`, and window 15 compatible but unattained.
Diagnostic run `31323643490` failed only at nonnegativity of the explicit
amplitude majorant; corrected diagnostic run `31323857109` passed but did not
retire PRE-VALIDATION.  Only the cold run above did.

### Step 7.5cxiv fixed-rate physical owner bound (SEALED; exact Fourier/Green identity and `B0` open)

Exact source checkpoint `082833d9ec4f410403beb5f8cfe2b2551379f11b`
passed cold GitHub Actions run
[`31326801633`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31326801633)
with workflow checkpoint `6e0cf31727ee6f93cf90f782f1f5398906c40512`.
The run recorded `COLD_MODE=true`; restoration and saving of `.lake/build`
were both skipped.  The first focal completed 8,601 jobs from `17:37:29Z` to
`18:06:10Z`; the remaining two focals and all three audits ended at
`18:07:24Z`.  Every stage exited zero.  All nine audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Downloaded artifact `9042129723`, named
`fixed-rate-physical-owner-bound-082833d9ec4f410403beb5f8cfe2b2551379f11b`,
has GitHub digest
`95630cc66f3d330fcaf3dad104a3fb3fb87603d34d50b6317258fee8c3284511`.
Its deterministic inner archive re-hashed on Windows to
`27c6b208017a69693d6a0469052c911e2ffed53a8d134957a76675f57a0d5d41`,
identical to the cold-run hash; all 17 entries of its `SHA256SUMS` manifest
also re-hashed exactly.

The sealed metric producer proves the complementary comparison
`ownerDist <= fineDist <= transportL1`.  It retains the fixed positive owner
rate `rho`, removes the depth-dependent block-boundary coefficient of the
inverse-scale route, and recombines the two independently shifted physical
endpoints with the literal one-link cost `1 + exp rho`.  The resulting bound
for the normalized stabilized integral therefore has a coefficient independent
of localization depth.

Primary-source scope remains narrower than the old generic Green label.
CMP89 (2.49), visually checked on printed page 585, is the normalized Holder
difference of the left derivative of `G_j Q_j^*`.  The sealed integral has
that source-shaped Fourier integrand, but its exact equality to the physical
Green operator is still an open Fourier/operator dictionary.  Consequently
the uniform coefficient is not yet installed as the complete physical `B0`;
window 15 remains compatible but unattained, every terminal field remains
open, and counters stay exactly `20/41`, `TermSource = 0`.

Diagnostic runs `31326152616` and `31326423001` exposed only arithmetic and
lemma-name elaboration in the forward metric proof.  Corrected diagnostic run
`31326627846` passed but did not retire PRE-VALIDATION.  Only the cold run
above did.

### Step 7.5cxv Fourier left-derivative kernel realization (SEALED; Fourier/operator dictionary and `B0` open)

Exact source checkpoint `8bc8fafb38608635740ba971ea43301befa23a60`
passed cold GitHub Actions run
[`31329783046`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31329783046)
with workflow checkpoint `a370a5d10a5818420865ed2f25f9b32bddf9bacc`.
The run completed in `20m5s`; restoration and saving of `.lake/build` were
both skipped.  The focal and audit exited zero, and all five audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9042818217`, named
`fourier-left-derivative-kernel-8bc8fafb38608635740ba971ea43301befa23a60`,
has GitHub digest
`3cec8607bbdfd58eb8ce96ae7865e6f84129218b3497882d664af136f51f9b0b`.
Its deterministic inner archive re-hashed on Windows to
`49758c057ff0f73d1e6b92d9ea01fafe50103460d4e42e9beb193268775e9d71`;
all 13 entries of its `SHA256SUMS` manifest also re-hashed exactly.

The sealed producer constructs an alpha-free Fourier endpoint kernel directly
from the printed phase, endpoint amplitude and stabilized denominator.  A
literal unit Holder edge removes the normalization internally.  The complete
source-normalized stabilized integral is then proved to be exactly the
difference of two values of this internally constructed Fourier kernel; no
endpoint family, physical Green, or operator equality is accepted as input.

This is only the Fourier side of CMP89 (2.49).  Identification with
`partial_mu^xi (G_j Q_j^*)` still requires the zero-background spectral
inverse, averaging/fibre, reflection/restriction and CMP95/CMP96/CMP99
dictionaries.  The physical `B0`, window-15 attainment, every terminal field
and `TermSource` remain open.  Counters stay exactly `20/41`,
`TermSource = 0`.  Diagnostic run `31329398921` exposed only the unsimplified
complex inverse of one; corrected cached run `31329620966` passed but did not
retire PRE-VALIDATION.  Only the cold run above did.

### Step 7.5cxvi fine-lattice phase-scale no-go (SEALED; rescaled Fourier/operator dictionary open)

Exact source checkpoint `0b967fe919cd7abde43f3ebdde2d43849cac845d`
passed cold GitHub Actions run
[`31331278818`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31331278818)
with workflow checkpoint `31bf02f62bc6e311bdb5c5b3fa1e994103b22716`.
The job completed in `14m55s`; restoration and saving of `.lake/build` were
both skipped.  The focal ran from `19:20:16Z` to `19:33:01Z`, the audit ended
at `19:33:06Z`, and both stages exited zero.  All three audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9043172950`, named
`fine-phase-scale-nogo-0b967fe919cd7abde43f3ebdde2d43849cac845d`,
has GitHub digest
`4f0e98b1a0ea7ee2a07af9741f62ec2ceed693abfd04423823b3eb004796456a`.
Its deterministic inner archive re-hashed on Windows to
`9e57fcd35ec3d97116e549753fcdbef5a489a1e75ac4b45e942221c93d8e664f`;
all 13 entries of its `SHA256SUMS` manifest also re-hashed exactly.

Primary visual inspection of CMP89 printed pp. 582 and 584--585 fixes the
physical endpoint lattice as `xi Z^d`, with `xi = L^(-j)`.  Hence an integer
fine-site displacement `u` represents the physical displacement `xi*u`.
The sealed theorem proves the exact scale transport from displacement to
momentum and gives the literal counterexample `xi=1/2`, alias `m=1`, `u=1`:
the alias phase is `exp(i*pi)=-1`, not one.  Therefore the already sealed
unit-lattice phase cancellation cannot be installed definitionally as the
physical phase dictionary of (2.49).

This is a reclassification, not a retraction of the algebra.  The integer
phase factorization and its downstream bounds remain compiler-verified on
their stated integer displacements.  Steps 7.5cviii--7.5cxv are now classified
as algebraic/unit-index specializations rather than physical CMP89 producers
until one rescaled dictionary transports the phase, derivative symbol,
averaging factors and endpoint normalization together.  The earlier contour
and holomorphy bricks formulated for real displacements are not refuted.
Physical `B0`, window-15 attainment, every terminal field and `TermSource`
remain open.  Counters stay exactly `20/41`, `TermSource = 0`.

Cached diagnostic run `31331110156` passed but did not retire PRE-VALIDATION.
Only the cold run above did.

### Step 7.5cxvii fine-lattice phased noncentral sum (SEALED; central assembly and physical Green dictionary open)

Exact source checkpoint `db534f72e38422c315cad6bd64d594a7454a9671`
passed cold GitHub Actions run
[`31332625049`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31332625049)
with workflow checkpoint `10d6fb55cc852493d16a2de42283b88c1a380777`.
The job completed in `15m18s`; restoration and saving of `.lake/build` were
both skipped.  The focal ran from `19:50:51Z` to `20:03:56Z`, the audit ended
at `20:04:01Z`, and both stages exited zero.  Both audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9043545832`, named
`fine-lattice-phased-noncentral-sum-db534f72e38422c315cad6bd64d594a7454a9671`,
has GitHub digest
`d019fa972ffbf457e4b4569d9c13f3ee16711239ad9da898708b2e78d30bba33`.
Its deterministic inner archive re-hashed on Windows to
`40c0ab7ff9ed9675e4c10ae8b5b088ce9947df777f1f239579cd047f99b12fac`;
all 13 entries of its `SHA256SUMS` manifest also re-hashed exactly.

The producer retains the literal alias-dependent endpoint phase inside every
noncentral summand of CMP89 (2.49).  On the signed physical contour all aliases
have the same exact norm because their shifts are real.  The pointwise source
weight can therefore be summed exactly as before, yielding
`exp(-rho*||u||_1) * quotientSumBound(rho)` with no alias-cardinality factor,
no loss of rate and no unit-lattice periodicity premise.

This is the source-faithful replacement for the noncentral use of the common
phase factorization.  Central-branch assembly, the complete endpoint bound,
normalized integration and the Fourier-to-physical Green dictionary remain
open.  Physical `B0`, window-15 attainment, every terminal field and
`TermSource` remain open.  Counters stay exactly `20/41`, `TermSource = 0`.
Cached diagnostic run `31332474918` passed but did not retire PRE-VALIDATION;
only the cold run above did.

### Step 7.5cxviii fine-lattice stabilized endpoint bound (SEALED; physical seam and integration open)

Exact source checkpoint `902ed1f06b29568a698c9dfac5856656035ca83e`
passed cold GitHub Actions run
[`31333611513`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31333611513)
with workflow checkpoint `08fd46ec7b4bfd1e221ab04893cfb0f7da7516a7`.
The job completed in `18m23s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `20:13:10Z` to `20:29:39Z`, the audit ended
at `20:29:46Z`, and both stages exited zero. All four audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9043872130`, named
`fine-lattice-stabilized-endpoint-bound-902ed1f06b29568a698c9dfac5856656035ca83e`,
has GitHub digest
`b3111775118f19948e27433d71e2b94a5213a55a7e17bf6cbd2f39e831398a0a`.
Its deterministic inner archive re-hashed on Windows to
`31210d1ed0e052070e09da674685872d00661a9bd7930d554f44a89102fb51e4`;
all 13 entries of its `SHA256SUMS` manifest re-hashed exactly.

The sealed producer assembles the central branch with the source-faithful
phase-retaining noncentral sum at the literal specialization `alpha = 0`.
It proves one exact physical endpoint decay
`exp(-rho*||u||_1)` times the visible central/noncentral amplitude and
stabilized reciprocal majorant. No common alias phase, alias-cardinality
factor, rate loss or unit-edge premise enters the estimate.

This is a pointwise Fourier-integrand bound only. The old four-coordinate
seam is specialized to unit-lattice displacements; a source-faithful seam for
physical `u/(L^j)` must be proved before normalized integration is inherited.
The physical Green dictionary, complete `B0`, window-15 attainment and every
terminal field remain open. Counters stay exactly `20/41`, `TermSource = 0`.
Cached diagnostic run `31333497194` passed but did not retire PRE-VALIDATION;
only the cold run above did.

### Step 7.5cxix physical fine-lattice phase seam (SEALED; displayed endpoint seam open)

Exact source checkpoint `50f5befa816642d5099bc231a1e073c555519bac`
passed cold GitHub Actions run
[`31335057233`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31335057233)
with workflow checkpoint `0bc0a52009275988aac17613b63f309ebbdff277`.
The job completed in `18m24s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `20:47:12Z` to `21:03:35Z`, the audit ended
at `21:03:41Z`, and both stages exited zero. All three audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9044288311`, named
`fine-lattice-phase-seam-50f5befa816642d5099bc231a1e073c555519bac`,
has GitHub digest
`745652961b5ac649d819eb8742a227848b385f0ea2efd3b69bd0e9b09ed2fbe4`.
Its deterministic inner archive re-hashed on Windows to
`6d6e187325414f0b229e1b98ed7568d1d0761b3d01f04324f5ee2d7aa0502d3f`;
all 13 manifest entries re-hashed exactly.

The seam input is now literal: a centered-alias wrap contributes momentum
`2*pi*N`, a physical fine displacement is `u/N`, and their product is the
integer phase `2*pi*u`. Endpoint Fourier phases are therefore invariant under
the alias-cycle wrap without identifying any individual `2*pi` alias phase
with one. This is compatible with, and does not weaken, the sealed no-go.

Only the phase seam is closed. Periodicity of the complete displayed endpoint,
transfer to the stabilized endpoint, the four-coordinate contour telescope,
normalized integration and recombination remain four named downstream bricks.
Physical `B0`, window 15 and terminal fields remain open. Counters stay exactly
`20/41`, `TermSource = 0`. Diagnostic run `31334904027` passed but did not
retire PRE-VALIDATION; failed diagnostics `31334576819` and `31334746446`
remain preserved as elaboration evidence.

### Step 7.5cxx fine-lattice displayed endpoint period (SEALED; stabilized seam open)

Exact source checkpoint `39598f7a567d268f27f57fed681800e7efce0815`
passed cold GitHub Actions run
[`31336314604`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31336314604)
with workflow checkpoint `335ec788847335672b33d50967b05f288dc012a1`.
The job completed in `19m17s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `21:16:19Z` to `21:33:34Z`, the audit ended
at `21:33:41Z`, and both stages exited zero. All six audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9044670652`, named
`fine-lattice-displayed-endpoint-period-39598f7a567d268f27f57fed681800e7efce0815`,
has GitHub digest
`80a0494a907d5fd1a0cf71ef63315fd7cd11d69a1b2b935cf5eb322a19ba11bb`.
Its deterministic inner archive re-hashed on Windows to
`f61257c543475262b014aa996cc963490da8be5f9592f0bc359ee3b139d05394`;
all 13 manifest entries re-hashed exactly.

At the literal specialization `alpha = 0`, the endpoint phase is evaluated
on `u/(L^j)`. The centered-alias wrap is transported through the scaled
difference, averaging amplitude, fine Laplacian and common denominators, and
the exact alias-cycle permutation proves periodicity of the complete displayed
endpoint sum. The holder displacement is not constrained: it disappears only
because its exponent is literally zero.

This does not assert global periodicity of the stabilized extension. Transfer
through the displayed/stabilized equality on the non-singular polydisc,
boundary seam, the 4D telescope, normalized integration and two-endpoint
recombination remain named downstream bricks. Physical `B0`, window 15 and
terminal fields remain open. Counters stay exactly `20/41`, `TermSource = 0`.
Diagnostic run `31336183990` passed with a restored graph but did not seal;
only the cold run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxxv physical Lie-fibre complexification (SEALED; generated Q' symbol open)

Exact source checkpoint `cd7234484dae807c3bb21190aa68cbab55f9a661`
passed cold GitHub Actions run
[`31365940121`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31365940121)
with workflow checkpoint `27eac7f350add18978d1433f79a41e54cd43f967`.
The cold job ran from `07:27:42Z` to `07:46:06Z` (`18m24s`);
restoration and saving of `.lake/build` were both skipped. The focal ran from
`07:29:53Z` to `07:45:55Z`, the audit ended at `07:46:01Z`, and both stages
exited zero. All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the target emitted no warning or
error of its own.

Artifact `9054594768`, named
`physical-fibre-complexification-cd7234484dae807c3bb21190aa68cbab55f9a661`,
has GitHub digest
`e3812cedc4ae12f660dff5cc3f06d6d82f4f5633e3a3e06f1656b95b1de3e65e`.
Its deterministic inner archive re-hashed on Windows to
`d5c06a4f10ca368ed70df29556d7a155b5fc2c2f697e6c7fcc2a89ccb8e1a4e5`;
all 13 internal manifest entries matched.

The real physical fibre `SUNLieCoord Nc` is embedded coordinatewise by an
explicit real-linear injective map into `EuclideanSpace C (Fin (Nc^2-1))`.
That map commutes exactly with the sealed flat physical stencil. The
vector-valued complex-fibre Fourier mode is then diagonalized internally,
first by the literal character eigenvalue and finally by the printed CMP89
unit-lattice symbol. No complex fibre, mode family or eigenvalue is accepted
as an input.

This seal does not diagonalize the generated `Q'` term, construct its
adjoint symbol, prove inverse uniqueness or transport a Green operator to a
region. Physical `B0`, window 15 and every terminal field remain open;
counters stay exactly `20/41`, `TermSource = 0`. Failed diagnostic run
`31365448830` preserves the missing-PiLp-constructor error. Diagnostic PASS
`31365742122` restored and saved the graph and did not seal; only the cold
run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxi fine-lattice stabilized endpoint period (SEALED; boundary seam open)

Exact source checkpoint `eedbb4e7fb00f20c4978f96de3853fdc1c1f75eb`
passed cold GitHub Actions run
[`31337490432`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31337490432)
with workflow checkpoint `8f676c69df3c511333e02314fc4ccc77f841a339`.
The job completed in `19m05s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `21:43:28Z` to `22:00:35Z`, the audit ended
at `22:00:40Z`, and both stages exited zero. The audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`.

Artifact `9045001993`, named
`fine-lattice-stabilized-endpoint-period-eedbb4e7fb00f20c4978f96de3853fdc1c1f75eb`,
has GitHub digest
`bb431fafc350a37355e38bc8c495416ad7d409fe4070a3f15a3448b745849fcc`.
Its deterministic inner archive re-hashed on Windows to
`b4893b0ee596eb5ec9a907ec560011ded63f4de771980a20f218b4e9dc74cafe`;
all 13 manifest entries re-hashed exactly.

On the literal non-singular domain, the stabilized endpoint at `alpha = 0`
is identified with the displayed rational endpoint at both sides of the
physical period. Nonvanishing at the shifted endpoint is derived internally
from symbol periodicity and the centered-alias permutation; it is not a
second premise. Thus the sealed displayed fine-lattice period transfers
without asserting global periodicity of the stabilized extension.

The boundary seam still requires the full-polydisc nonvanishing producer at
every partially shifted stage. The 4D telescope, normalized integration,
two-endpoint recombination, physical `B0`, window 15 and terminal fields
remain open. Counters stay exactly `20/41`, `TermSource = 0`. Diagnostic run
`31337368565` passed with a restored graph but did not seal; only the cold run
above retired the two PRE-VALIDATION marks.

### Step 7.5cxxii fine-lattice stabilized boundary seam (SEALED; 4D telescope open)

Exact source checkpoint `72915aefdfcf886a0fc6afef915967bc34ad398e`
passed cold GitHub Actions run
[`31338609395`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31338609395)
with workflow checkpoint `dbcc098e2b987de8a324e6708aa43111059bb7d7`.
The job completed in `20m05s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `22:09:39Z` to `22:27:41Z`, the audit ended
at `22:27:46Z`, and both stages exited zero. The audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`.

Artifact `9045353338`, named
`fine-lattice-endpoint-boundary-seam-72915aefdfcf886a0fc6afef915967bc34ad398e`,
has GitHub digest
`404288ac8d2f1a85b358a307307008849a92f105650694a50717d4532b7c9cf4`.
Its deterministic inner archive re-hashed on Windows to
`da913a0b5ba47ac0d917c68142fe473937a14c8ae5d73a2c051d9712b46ece64`;
all 13 manifest entries re-hashed exactly.

The boundary seam consumes the existing displayed-domain producer with the
literal hypothesis `forall k, |Im z_k| <= rho`. Thus it remains valid when
coordinates preceding the active one are already shifted to signed imaginary
faces. It then invokes the sealed fine-lattice stabilized period at physical
endpoint `u/(L^j)`. No one-coordinate-only nonvanishing premise or global
periodicity family is introduced.

The gate identified before iteration is closed. The one-coordinate shift,
product integrability, 4D telescope, normalized integration and two-endpoint
recombination remain open. Physical `B0`, window 15 and terminal fields remain
open. Counters stay exactly `20/41`, `TermSource = 0`. Diagnostic run
`31338486247` passed with a restored graph but did not seal; only the cold run
above retired the two PRE-VALIDATION marks.

### Step 7.5cxxiii one-coordinate fine-lattice endpoint shift (SEALED; product iteration open)

Exact source checkpoint `290d546550a55511d7677ce67066ca403afdc393`
passed cold GitHub Actions run
[`31339761858`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31339761858)
with workflow checkpoint `e2d15918ea1cb630d49e304ba5a53c4fae9b648f`.
The job completed in `16m43s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `22:36:51Z` to `22:51:45Z`, the audit ended
at `22:51:50Z`, and both stages exited zero. The audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`.

Artifact `9045653286`, named
`fine-lattice-endpoint-coordinate-shift-290d546550a55511d7677ce67066ca403afdc393`,
has GitHub digest
`2187b613be4796282c61bbd933124917d0b9540ec660caf208eef1c46f0a79a8`.
Its deterministic inner archive re-hashed on Windows to
`9eb80f43db59a1517a8d32c94fdd0002f2e0f817cd7a555745b56e988188a928`;
all 13 manifest entries re-hashed exactly.

The rectangular Cauchy theorem is specialized to `alpha = 0` and endpoint
`u/(L^j)`. Endpoint holomorphy is constructed from the common-radius producer,
and the two vertical faces are identified by the sealed full-polydisc seam.
The proof treats dependent coordinates by the explicit cases `k = nu` and
`k != nu`; it accepts neither a holomorphic endpoint family nor a seam family.

This closes one coordinate only. Compact-product integrability, iteration over
all four coordinates, normalized integration and endpoint recombination remain
open. Physical `B0`, window 15 and terminal fields remain open. Counters stay
exactly `20/41`, `TermSource = 0`. Diagnostic run `31339628367` passed with a
restored graph but did not seal; only the cold run above retired the two
PRE-VALIDATION marks.

### Step 7.5cxxiv fine-lattice endpoint product telescope (SEALED; normalized integration open)

Exact source checkpoint `4b1dfb64060554c673389a4ad058aee7cc4804a0`
passed cold GitHub Actions run
[`31340883542`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31340883542)
with workflow checkpoint `0c41380dc00846ebc7a19a001afd7433388563e9`.
The job completed in `19m42s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `23:04:04Z` to `23:21:41Z`, the audit ended
at `23:21:53Z`, and both stages exited zero. All five audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9046019010`, named
`fine-lattice-endpoint-product-telescope-4b1dfb64060554c673389a4ad058aee7cc4804a0`,
has GitHub digest
`7420717e2a0baeb0579df1f55e095f2987f73ac58443785c3a087f3175fe71ed`.
Its deterministic inner archive re-hashed on Windows to
`693c6c5c77e0362fa660c62112681e5a02dd024be19480f737fa2b4c2bc3c3a4`;
all 13 manifest entries re-hashed exactly.

The brick constructs product integrability for every partial signed stage and
then applies the sealed one-coordinate fine-lattice shift four times. The
nonvanishing hypothesis is the complete-polydisc condition `forall k,
abs (Im (z k)) <= rho`, so earlier shifted coordinates remain admissible at
every later stage. Each endpoint receives its own signed contour; no common
sign for two endpoints and no family of slice equalities are assumed.

This closes one endpoint's literal 4D product iteration only. Source-normalized
integration, the two-endpoint recombination, the unit-edge comparison lemma,
physical `B0`, window 15 and terminal fields remain open. Counters stay exactly
`20/41`, `TermSource = 0`. Diagnostic run `31340764824` passed with a restored
graph but did not seal; only the cold run above retired the two PRE-VALIDATION
marks.

### Step 7.5cxxv normalized fine-lattice endpoint integral (SEALED; recombination open)

Exact source checkpoint `e281517bd3537c7fb244355421c03575912b6011`
passed cold GitHub Actions run
[`31342326880`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31342326880)
with workflow checkpoint `a3849fb3b87544c237502b140e6c82c5aea296c0`.
The job completed in `17m35s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `23:39:04Z` to `23:54:17Z`, the audit ended
at `23:54:26Z`, and both stages exited zero. All seven audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9046404157`, named
`normalized-fine-lattice-endpoint-integral-e281517bd3537c7fb244355421c03575912b6011`,
has GitHub digest
`d95f02e2ebe95df886e684e25bc8a43e20573aa9a431b06a29ce980a4adc012d`.
Its deterministic inner archive re-hashed on Windows to
`f86d57f5bc283450889f1e16d13decefbefeefae2d12c0304bab375f255efc5f`;
all 13 manifest entries re-hashed exactly.

The source normalization `(2*pi)^(-4)` is applied to the sealed physical
fine-lattice endpoint telescope and cancels the translated Brillouin-cube
volume exactly. The endpoint bound retains the literal physical displacement
`(L^j)^(-1) u`. A named scale lemma proves that a unit fine edge costs exactly
`exp (rho * (L^j)^(-1))`, rather than silently inheriting the unit-lattice
factor `exp rho`.

This closes one normalized endpoint only. Exact subtraction of the two
independently shifted endpoints, the physical unit-bond producer, the
Fourier/operator dictionary, physical `B0`, window 15 and terminal fields
remain open. Counters stay exactly `20/41`, `TermSource = 0`. Diagnostic run
`31342182306` passed with a restored graph but did not seal; failed diagnostic
run `31342007885` remains preserved as an elaboration failure. Only the cold
run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxvi normalized fine-lattice endpoint recombination (SEALED; physical Green dictionary open)

Exact source checkpoint `335af26bb8959b7c0692963d251d635cc12843ce`
passed cold GitHub Actions run
[`31343838078`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31343838078)
with workflow checkpoint `64c363330558559f0ce1d3370622831ebf618c5f`.
The job completed in `20m23s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `00:14:45Z` to `00:33:04Z`, the audit ended
at `00:33:16Z`, and both stages exited zero. All seven audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9046938975`, named
`normalized-fine-lattice-recombination-335af26bb8959b7c0692963d251d635cc12843ce`,
has GitHub digest
`bb3089dd249da5c8f7cf75dc764a99d3da1a4b9b31595248144608e1d2b64527`.
Its deterministic inner archive re-hashed on Windows to
`030eebf71c763b4bfb312c2a285e2400974691e1a2b89f1efe7f04ed1930ca49`;
all 13 manifest entries re-hashed exactly.

The complete normalized stabilized integral is proved to be the exact
difference of two endpoint integrals after shifting each endpoint along its
own signed contour. Integrability and both contour equalities are constructed
internally. The norm bound retains the sum of the two literal physical
fine-lattice weights; a separate theorem compares them with the exact visible
cost `exp (rho * (L^j)^(-1))` for a unit fine edge. No common endpoint sign
and no unnamed neighbor constant are introduced.

Installation of the already sealed physical-bond and fine-site dictionaries,
the identification with `partial_mu^xi (G_j Q_j^*)`, physical `B0`, window 15
and terminal fields remain open. Counters stay exactly `20/41`,
`TermSource = 0`. Diagnostic run
`31343695361` passed with a restored graph but did not seal; failed diagnostic
runs `31343318299` and `31343514391` remain preserved as elaboration failures.
Only the cold run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxvii physical fine normalized owner bound (SEALED; uniform coefficient and Green dictionary open)

Exact source checkpoint `e8964e0247c072bda948a48e385b063f924ca4c7`
passed cold GitHub Actions run
[`31345479919`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31345479919)
with workflow checkpoint `2b9139b530c088aadcaeae03aff26c0f26aa6b59`.
The job completed in `28m07s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `00:51:35Z` to `01:17:39Z`, the audit ended
at `01:17:46Z`, and both stages exited zero. All three audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9047557376`, named
`physical-fine-normalized-owner-bound-e8964e0247c072bda948a48e385b063f924ca4c7`,
has GitHub digest
`4f404c3d4386322ca5c8ea62a80c31f66d50780b1b2768eb41baefb5ce560e54`.
Its deterministic inner archive re-hashed on Windows to
`63d6424e3b0524535273ae033e9e2ccd02a466c15ffe6e55b4c9473a3cabf033`;
all 13 manifest entries re-hashed exactly.

The already sealed physical unit-bond and fine-site displacement dictionaries
are installed in the source-normalized recombination. At fine spacing
`xi = (L^(depth+1))^(-1)`, the inverse-scale bridge proves the exact identity
`(rho*xi)*L^(depth+1) = rho`, so the resulting decay has the fixed owner rate
`rho`. The coefficient keeps both costs visible: the neighboring-endpoint
factor `1+exp(rho*xi)` and the inverse-scale block-boundary factor
`exp((rho*xi)*2*(L^(depth+1)-1))`.

This is infrastructure below the physical CMP89 Green certificate, not a
terminal field. A depth-uniform simplification of the displayed coefficient,
the Fourier/operator identification with the printed Holder difference of
`partial_mu^xi (G_j Q_j^*)`, physical `B0`, window 15 and terminal fields
remain open. Counters stay exactly `20/41`, `TermSource = 0`. Diagnostic run
`31345330119` passed with a restored graph but did not seal; failed diagnostic
run `31345138516` remains preserved as an elaboration failure. Only the cold
run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxviii uniform physical fine normalized owner bound (SEALED; fine Fourier/Green dictionary open)

Exact source checkpoint `27e975e36ac3c7a5aa36d1e3db8217aa677342d8`
passed cold GitHub Actions run
[`31347364638`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31347364638)
with workflow checkpoint `a11403b06907384e3e06dc35b6da08c7f5f9a800`.
The job completed in `31m01s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `01:34:33Z` to `02:03:30Z`, the audit ended
at `02:03:38Z`, and both stages exited zero. All four audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9048221362`, named
`physical-fine-uniform-normalized-owner-bound-27e975e36ac3c7a5aa36d1e3db8217aa677342d8`,
has GitHub digest
`c58bb238c097d15ff8b0f668a833a5435effabb56fe3614269bfbc9ecb41c9a0`.
Its deterministic inner archive re-hashed on Windows to
`4796efa76f0485741c79c010afa7547a6132479384017ce1e2e9fe289fb5c9f1`;
all 13 manifest entries re-hashed exactly.

The literal fine coefficient from Step 7.5cxxvii is now bounded uniformly in
`depth`. The endpoint exponent uses `rho*xi <= rho`; the inverse-scale
boundary exponent uses
`(rho*xi)*2*(L^(depth+1)-1) <= 2*rho`. Thus the source-shaped physical fine
integral has the explicit depth-independent coefficient
`(1+exp rho)*exp(2*rho)*endpointAmplitude` at fixed owner rate `rho`.

The older integer-displacement Fourier kernel cannot serve as this endpoint:
it encodes unit-lattice phases and would reintroduce the sealed phase-scale
no-go. A separate fine-lattice Fourier kernel and its equality with the
printed Holder difference of `partial_mu^xi (G_j Q_j^*)` remain open. Hence
this coefficient is not yet the complete physical `B0`; window 15 and all
terminal fields remain open. Counters stay exactly `20/41`, `TermSource = 0`.
Diagnostic run `31347240982` passed with a restored graph but did not seal;
failed diagnostic `31347092998` remains preserved as an elaboration failure.
Only the cold run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxix fine-lattice Fourier left-derivative kernel (SEALED; physical Green dictionary open)

Exact source checkpoint `8532124d6a387cbd2459fe2c5c377e5599db1242`
passed cold GitHub Actions run
[`31349337028`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31349337028)
with workflow checkpoint `e084acbfd5b83fb09ef006f50fec8821c2ddcf69`.
The job completed in `16m38s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `02:18:23Z` to `02:32:45Z`, the audit ended
at `02:32:53Z`, and both stages exited zero. All six audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9048630196`, named
`fine-lattice-fourier-left-derivative-kernel-8532124d6a387cbd2459fe2c5c377e5599db1242`,
has GitHub digest
`89660b103325ac3336f39808781bc99b4c23b963014bde9734717e39b50e16b1`.
Its deterministic inner archive re-hashed on Windows to
`41c6c7bebedae397152750c9fc90c7ef147d02d210049a833d103d2007b3462a`;
all 13 internal manifest entries matched.

At the literal `alpha = 0` specialization the endpoint integrand is now
proved independent of the Holder displacement. A separate fine-lattice
Fourier kernel is constructed at the physical endpoint displacement
`(L^j)^(-1) * u`; every normalized physical endpoint is identified with that
kernel, and the complete normalized stabilized expression is proved exactly
equal to the difference of the two independently constructed endpoint kernel
values. The older integer-displacement kernel is not imported or reused.

This seals the source-shaped fine Fourier expression, not its identification
with the repository's literal operator `partial_mu^xi (G_j Q_j^*)`. That
operator dictionary, physical `B0`, window 15 and terminal fields remain
open. Counters stay exactly `20/41`, `TermSource = 0`. Diagnostic run
`31349187530` passed with a restored graph but did not seal; only the cold run
above retired the two PRE-VALIDATION marks.

### Step 7.5cxxx fine-lattice Fourier Green forward difference (SEALED; integral/operator dictionary open)

Exact source checkpoint `531032b6bec993e56129e443c3a2463dd61b54be`
passed cold GitHub Actions run
[`31352539505`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31352539505)
with workflow checkpoint `0162dc26e9ef8169db146b311f3f20633e789da6`.
The job completed in `20m34s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `03:27:05Z` to `03:45:33Z`, the audit ended
at `03:45:42Z`, and both stages exited zero. All ten audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`; the sealed target emitted
no warning or error of its own.

Artifact `9049779786`, named
`fine-lattice-fourier-green-derivative-531032b6bec993e56129e443c3a2463dd61b54be`,
has GitHub digest
`cf55bb1e93218ff3488f69d9c3d41b8597a7b2861c58c5a5fb63d226bca2f2f5`.
Its deterministic inner archive re-hashed on Windows to
`92de0dd494e887b91685a121df902d5672dbf638482ce93bc0a20eddc30eedf3`;
all 13 internal manifest entries matched.

The literal stabilized Fourier Green value integrand is now constructed with
the same central cancellation, noncentral alias fibre and common denominator
as the sealed derivative integrand. A positive unit fine-site shift is
transported to the physical displacement `xi*e_mu`, and its pointwise forward
difference quotient is proved exactly equal to the printed
`D_xi(-q_mu) = (exp(i*xi*q_mu)-1)/xi` derivative integrand. The sign is a
theorem, not an inference from the word `left`.

This seals a pointwise Fourier identity only. Integrability of the Green value
integrand, transport of the difference through the normalized Brillouin
integral, and identification with the repository's literal `G_j Q_j^*`
remain open. Physical `B0`, window 15 and every terminal field remain open;
counters stay exactly `20/41`, `TermSource = 0`. Diagnostic PASS
`31351283751` did not seal. Failed diagnostics `31350838812` and
`31351062941`, and cold PASS `31351453287` on the warning-bearing predecessor,
remain preserved; only the warning-clean cold run above retired the two
PRE-VALIDATION marks.

### Step 7.5cxxxi normalized fine-lattice Fourier Green integral (SEALED; operator dictionary open)

Exact source checkpoint `414212ec8410c88fdb1dfe7bcb5081844e5f0903`
passed cold GitHub Actions run
[`31354841843`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31354841843)
with workflow checkpoint `72cb8ab07dfa5a707910037d14524414854fc528`.
The job completed in `20m19s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `04:15:56Z` to `04:34:16Z`, the audit ended
at `04:34:28Z`, and both stages exited zero. All seven audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`; the sealed target
emitted no warning or error of its own.

Artifact `9050601865`, named
`normalized-fine-lattice-fourier-green-414212ec8410c88fdb1dfe7bcb5081844e5f0903`,
has GitHub digest
`604a6c914fdc121ba60aba14f62853cd140f0026ee356a41a27f1794aa6b5472`.
Its deterministic inner archive re-hashed on Windows to
`a3d33492d63ca214ed45ee30c7618fab7d85bd294e46ce4fa59030b5ab3f8e29`;
all 13 internal manifest entries matched.

The literal stabilized Fourier Green value is now proved integrable on the
real Brillouin cube from the already sealed complete-polydisc nonvanishing
gate and compactness; no integrability premise is accepted. The
source-normalized Green integral is constructed internally, and its exact
positive fine-site forward quotient is proved equal to the sealed normalized
left-derivative kernel by moving the difference through the integral. The
full-polydisc condition remains `forall mu, |Im z_mu| <= rho`; it is not
weakened to a one-coordinate strip.

This does not identify the Fourier Green with the repository's literal
`G_j Q_j^*`. That remaining dictionary requires the periodic zero-background
specialization, Fourier diagonalization of the generated precision, the
symbol/adjoint dictionary for `Q'`, and inverse uniqueness before any
regional transport. Physical `B0`, window 15 and every terminal field remain
open. Counters stay exactly `20/41`, `TermSource = 0`. Diagnostic PASS
`31354670690` used a restored graph and did not seal. Failed diagnostics
`31354142299`, `31354327613` and `31354499576` remain preserved; only the
cold run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxxii flat generated ambient Laplacian (SEALED; Fourier diagonalization open)

Exact source checkpoint `d9c0cac633b9e8888fb2025a604300bd092c92dd`
passed cold GitHub Actions run
[`31356996075`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31356996075)
with workflow checkpoint `97ad8edf893517cfa6fcb97ae8644e3aa61493f1`.
The job completed in `22m53s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `04:57:14Z` to `05:18:12Z`, the audit ended
at `05:18:20Z`, and both stages exited zero. All four audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`; the sealed target emitted
no warning or error of its own.

Artifact `9051363785`, named
`flat-ambient-laplacian-d9c0cac633b9e8888fb2025a604300bd092c92dd`, has
GitHub digest
`8efd4eaf4668bf578ab12b0f8d4b22f8629a620b448079fbe300114cbf9ca265`.
Its deterministic inner archive re-hashed on Windows to
`bf13f2d5466eda9dd1a9bd165c13bff0dc0f15b8cee03f23a468fde3f11c0273`;
all 13 internal manifest entries matched.

The literal trivial gauge background is constructed by the canonical
`trivialPhysicalGaugeBackground`, not supplied as a free function. At that
background the complete CMP99 ambient covariant stencil is proved term by
term equal to the ordinary symmetric periodic nearest-neighbour stencil, and
the generated ambient operator retains exactly the two visible
`spacing⁻¹` factors. No positivity or nonzero-spacing premise is introduced.

This is the first non-circular operator-dictionary entry below the sealed
CMP89 Fourier integral. It does not Fourier-diagonalize the stencil, identify
the symbol or adjoint of `Q'`, prove inverse uniqueness, or transport the
result to a regional Green operator. Physical `B0`, window 15 and every
terminal field remain open. Counters stay exactly `20/41`,
`TermSource = 0`. Diagnostic PASS `31356849772` used a restored graph and did
not seal; failed diagnostics `31356282470`, `31356476316` and `31356678354`
remain preserved. Only the cold run above retired the two PRE-VALIDATION
marks.

### Step 7.5cxxxiii flat periodic Fourier stencil (SEALED; printed-symbol and physical complexification open)

Exact source checkpoint `a82d41ac41bb5ccbe86fd7554c5bdef06468d956`
passed cold GitHub Actions run
[`31360584905`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31360584905)
with workflow checkpoint `d75c5ce026ba97e9bacefeceb516c025d429d360`.
The job completed in `15m27s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `06:05:25Z` to `06:18:48Z`, the audit ended
at `06:18:54Z`, and both stages exited zero. All nine audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`; the sealed target
emitted no warning or error of its own.

Artifact `9052509105`, named
`flat-fourier-stencil-a82d41ac41bb5ccbe86fd7554c5bdef06468d956`, has
GitHub digest
`855381e975866515e56727dfa92c164d479d7da4afa402bc1374a11f60a16748`.
Its deterministic inner archive re-hashed on Windows to
`2e65d22a1864b5943231b54ea9cb6e3949020e754f04d09e9404b331597af1ab`;
all 13 internal manifest entries matched.

The literal `FinBox d N -> ZMod N` phase and Mathlib standard additive
character now give exact positive- and negative-shift laws. The scalar
complex symmetric nearest-neighbour stencil is diagonalized by those modes,
with the eigenvalue written as the sum of the positive and negative character
terms. Orientation and the `2*pi/N` normalization therefore enter through
the character itself rather than an unnamed Fourier convention.

This is a scalar complex stencil theorem. It does not yet identify the
character eigenvalue with the printed real CMP89 unit-lattice symbol, provide
an explicit complexification of the real `SUNLieCoord Nc` fibre, diagonalize
the `Q'` term, prove inverse uniqueness or transport to a regional Green
operator. Physical `B0`, window 15 and every terminal field remain open;
counters stay exactly `20/41`, `TermSource = 0`. Diagnostic PASS
`31360401684` used a restored graph and did not seal. Cold PASS
`31359048549` on the warning-bearing predecessor, diagnostic PASS
`31358894795`, and failed diagnostic `31358679426` remain preserved; only the
warning-clean cold run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxxiv flat character-to-printed-symbol dictionary (SEALED; physical complexification open)

Exact source checkpoint `67083c091614869de17f8c28132ab509a9bebf46`
passed cold GitHub Actions run
[`31363297991`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31363297991)
with workflow checkpoint `d14501b14ddba77cb090bfcd52c3e2f7c5846d5d`.
The cold job ran from `06:47:19Z` to `07:10:42Z` (`23m23s`);
restoration and saving of `.lake/build` were both skipped. The focal ended at
`07:10:30Z`, the audit at `07:10:38Z`, and both stages exited zero. All six
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`;
the sealed target emitted no warning or error of its own.

Artifact `9053704495`, named
`flat-fourier-symbol-67083c091614869de17f8c28132ab509a9bebf46`, has
GitHub digest
`56f812fbe99e5ee855f44a8ebf0d2d5b89c9a08a744203953102780328cdea67`.
Its deterministic inner archive re-hashed on Windows to
`7caff2c19bcf361eb260d73ee4c548ab39bd344907154ebc73b7825f9307b2e8`;
all 13 internal manifest entries matched.

The dictionary constructs the literal discrete momentum `2*pi*k/N`, proves
the positive and negative standard additive characters equal the corresponding
complex exponentials, and identifies their product with the opposite-momentum
entire unit-difference pairing. After the explicit spacing-one specialization,
the scalar complex stencil eigenvalue is exactly the printed real CMP89
unit-lattice Laplacian symbol. No Fourier sign, momentum normalization or
opposite-momentum product is accepted as an input.

This remains a scalar complex dictionary. It does not complexify the real
`SUNLieCoord Nc` fibre, diagonalize the generated `Q'` term, prove inverse
uniqueness or transport to a regional Green operator. Physical `B0`, window
15 and every terminal field remain open; counters stay exactly `20/41`,
`TermSource = 0`. Failed diagnostic runs `31362048764`, `31362313958`,
`31362542312` and `31362781143` preserve the elaboration corrections.
Diagnostic PASS `31363036192` restored and saved the graph and did not seal;
only the cold run above retired the two PRE-VALIDATION marks.

### Step 7.5cxxxvi flat one-block `Q'` Fourier amplitude (SEALED; physical mode action open)

Exact source checkpoint `c0bad89fd6bd4365dac40bd6fd8a9af070ce772b`
passed cold GitHub Actions run
[`31368645861`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31368645861)
with workflow checkpoint `8800307200cc6dc356eeb60cbdef98cd6efacd92`.
The cold job completed in `17m07s`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `08:08:51Z` to `08:23:52Z`, and the
audit ended at `08:23:59Z`. Both stages exited zero, all four declarations
use exactly `[propext, Classical.choice, Quot.sound]`, and the target emitted
no warning or error of its own.

Artifact `9055606077`, named
`flat-qprime-fourier-amplitude-c0bad89fd6bd4365dac40bd6fd8a9af070ce772b`,
has GitHub digest
`a0c066dd404a305d9894b47d84e9653b568071922da6cba5fcc95aec022f5df3`.
Its deterministic inner archive re-hashed on Windows to
`9aae33eccec082787a4fba72c3866ae94233baad60b8713d604bf6911ff06d53`;
all 13 internal manifest entries matched.

The producer expands the literal source coefficient
`cmp99SourceBlockAverageWeight M d = M^-d` over the complete `M^d` offset
fibre and proves its character sum exactly equal to the printed product of
coordinatewise CMP89 entire averaging factors. The opposite-momentum product
is retained without inserting complex conjugation away from the real slice.

This seal identifies only the scalar offset amplitude. It does not yet build
the offset-to-physical-block equivalence, prove the fine-to-coarse mode action
of `cmp99SourceTransportedBlockAverageCLM`, identify the weighted adjoint,
diagonalize `Q'^*Q'`, prove inverse uniqueness or transport to a regional
Green operator. Physical `B0`, window 15 and every terminal field remain
open. Counters stay exactly `20/41`, `TermSource = 0`. Failed diagnostic
`31368030280` remains preserved; diagnostic PASS `31368432187` used a
restored graph and did not seal. Only the cold run above retires the two
PRE-VALIDATION marks.

### Step 7.5cxxxvii internal-offset/physical-block equivalence (SEALED; mode action open)

Exact source checkpoint `819497118e773c78e67f6792dea652e749e7199c`
passed cold GitHub Actions run
[`31370770140`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31370770140)
with workflow checkpoint `a764a4da538978758bda5d358ac356bab3d8f543`.
The cold job completed in `17m07s`; restoration and saving of `.lake/build`
were skipped. The focal ran from `08:37:52Z` to `08:52:52Z`, and the audit
ended at `08:52:57Z`. Both stages exited zero, all three declarations use
exactly `[propext, Classical.choice, Quot.sound]`, and the target emitted no
warning or error of its own.

Artifact `9056434666`, named
`flat-qprime-block-offset-819497118e773c78e67f6792dea652e749e7199c`,
has GitHub digest
`ac03566cdac27fd4cc6f7bd05e967339274178ebab70eccfb6124907a1e51648`.
Its deterministic inner archive re-hashed on Windows to
`1b9ae477b095b848a12519d5fbe65acf6b411151fd9200099b09c0ea71bef14c`;
all 13 internal manifest entries matched.

The producer proves that `cmp99BlockEmbed` and
`cmp99BlockOffsetOfMem` are inverse on one complete owner block, packages
the result as a canonical equivalence, and derives the exact reindexing of a
block-site sum by `FinBox d M`. It reuses the existing active-region
block-owner decomposition and introduces no second cardinality or overlap
constant.

This carrier dictionary does not evaluate a Fourier mode, trivialize the
physical transport, identify the weighted adjoint, diagonalize `Q'^*Q'`,
prove inverse uniqueness or transport to a regional Green operator. Physical
`B0`, window 15 and all terminal fields remain open. Counters stay exactly
`20/41`, `TermSource = 0`. Failed diagnostic `31370258620` is preserved;
restored diagnostic PASS `31370540139` did not seal. Only the cold run above
retires PRE-VALIDATION.

### Step 7.5cxxxviii exact flat one-block `Q'` Fourier-mode action (SEALED; coarse alias open)

Exact source checkpoint `811bbd4e3bb66d9f16df165f8f976a47cfc08dae`
passed cold GitHub Actions run
[`31373952680`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31373952680)
with workflow checkpoint `708d825b4d5bc8d3f2bd2a061c54ba694b6b15ff`.
The cold job completed in `23m42s`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `09:20:08Z` to `09:41:49Z`, and the
audit ended at `09:41:56Z`. Both stages exited zero, all nine audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`, and the
target emitted no warning or error of its own.

Artifact `9057854933`, named
`flat-qprime-fourier-mode-action-811bbd4e3bb66d9f16df165f8f976a47cfc08dae`,
has GitHub digest
`a903728e30fbf7ffc30bc7b97d9b7bd45616d2fbefd24db1112d2064e97867fd`.
Its deterministic inner archive re-hashed on Windows to
`f45497f8fe831ed8b3d84470247d9ffc24edefa4b8e56b882520a0f64dbe7704`;
all 13 internal manifest entries matched.

The producer factors the literal fine Fourier character at `cmp99BlockEmbed`
into its block-basepoint and internal-offset phases, identifies the latter
with the sealed CMP89 amplitude at the explicit momentum `-M * p_fine`, and
proves the exact source-normalized `M^-d` sum over one complete owner block.
The remaining factor is still the fine mode evaluated at the literal block
basepoint: no coarse mode, reciprocal alias, physical Lie-fibre action,
weighted adjoint or `Q'^*Q'` diagonalization is inferred.

This brick introduces no second block cardinality, row mass or normalization.
Physical `B0`, window 15 and all terminal fields remain open. Counters stay
exactly `20/41`, `TermSource = 0`. Failed diagnostics `31372848347`,
`31373122676` and `31373438940` remain preserved; restored diagnostic PASS
`31373704872` did not seal. Only the cold run above retires the two
PRE-VALIDATION marks. The next honest brick fixes the coarse reciprocal alias
and proves that the surviving block-basepoint phase is the corresponding
coarse Fourier mode.

### Step 7.5cxxxix coarse reciprocal alias and exact coarse-mode action (SEALED; physical fibre action open)

Exact source checkpoint `297b79c636bf246dedc20f72596a603103d2beab`
passed cold GitHub Actions run
[`31377161152`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31377161152)
with workflow checkpoint `bfe432c62ac87bda4d4cdacc8d26e990b53784b6`.
The cold job completed in `22m23s`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `10:01:38Z` to `10:22:12Z`, and the
audit ended at `10:22:18Z`. Both stages exited zero. The first two audited
declarations depend only on `[propext]`; the remaining four use exactly
`[propext, Classical.choice, Quot.sound]`. The target emitted no warning or
error of its own.

Artifact `9059009193`, named
`flat-qprime-coarse-alias-297b79c636bf246dedc20f72596a603103d2beab`,
has GitHub digest
`9b99a16860cbd13b886267547248576462e3c75bc264f3c2c71665aa4af7ed83`.
Its deterministic inner archive re-hashed on Windows to
`196f057a7e129394f528b8d5470e8d075c798c4dff8bf123ea325f7939fb583b`;
all 13 internal manifest entries matched.

The producer constructs the coarse reciprocal alias coordinatewise as
`k_mu mod N'`, proves the restriction of the standard character from the
fine torus at `M*y` to the corresponding coarse character, and rewrites the
surviving block-basepoint phase as the literal coarse Fourier mode. Combined
with the preceding brick, one source-normalized flat block average therefore
maps a fine Fourier mode to the CMP89 amplitude times that constructed coarse
mode. No alias, phase equality or Fourier-family identification is supplied
as data.

This is still scalar complex algebra. Physical Lie-fibre action, the weighted
adjoint, `Q'^*Q'`, inverse uniqueness and regional transport remain open.
Physical `B0`, window 15 and all terminal fields remain open. Counters stay
exactly `20/41`, `TermSource = 0`. Failed diagnostic `31376562811` preserves
the redundant-tactic and unused-instance corrections. Restored diagnostic
PASS `31376937385` did not seal; only the cold run above retires the two
PRE-VALIDATION marks. The next honest brick transports this exact action to
the already sealed explicit physical-fibre complexification without yet
identifying the weighted adjoint.

### Step 7.5cxl exact flat `Q'` action in the complexified physical fibre (SEALED; transported CLM open)

Exact source checkpoint `5eec68ba158e3fb0de006130fc40e66a0215e9ed`
passed cold GitHub Actions run
[`31379326913`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31379326913)
with workflow checkpoint `512bac4865882e6c4688bd01338d403c8275276e`.
The cold job completed in `14m59s`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `10:31:10Z` to `10:44:02Z`; the audit
ended at `10:44:07Z`. Both stages exited zero, all three declarations use
exactly `[propext, Classical.choice, Quot.sound]`, and the target emitted no
warning or error of its own.

Artifact `9059626063`, named
`flat-qprime-complex-fibre-mode-action-5eec68ba158e3fb0de006130fc40e66a0215e9ed`,
has GitHub digest
`6c3615d1d77b937daef259a4cfa380c396d12ec46e1362e3859468a9965978aa`.
Its deterministic inner archive re-hashed on Windows to
`afa1907fbd71c437e9e821460a7cd3c26dde204338077efe00c51802c54d3caf`;
all 13 internal manifest entries matched.

The producer transports the exact scalar one-block action to
`SUNLieComplexCoord Nc`, proves the corresponding block-basepoint alias
identity for vector-valued Fourier modes, and supplies a corollary whose
fibre vector is constructed internally as the image of an actual
`SUNLieCoord Nc` vector under the sealed coordinatewise complexification.
No complex-fibre identification or Fourier family is supplied as data.

This is the flat identity-transport block sum, not yet the literal
active-region `cmp99SourceTransportedBlockAverageCLM`: contour-holonomy
transport, its weighted adjoint, the finite alias-fibre matrix for `Q'^*Q'`,
inverse uniqueness and regional transport remain open. Physical `B0`, window
15 and all terminal fields remain open. Counters stay exactly `20/41`,
`TermSource = 0`. Diagnostic PASS `31379102294` restored the graph and did
not seal; only the cold run above retires the two PRE-VALIDATION marks. The
next source-faithful gate is the finite carrier equivalence between fine
momenta with fixed coarse alias and `CMP89Eq246AliasIndex`, before any
weighted-adjoint matrix identity is attempted.

### Step 7.5cxli fixed-coarse fine-momentum fibre to centered CMP89 alias fibre (SEALED; amplitude-period dictionary open)

Exact source checkpoint `2a99a8997763597e7faac87c6455163c3df3ec99`
passed cold GitHub Actions run
[`31382323118`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31382323118)
with workflow checkpoint `0c7a5d9f33d881218d6482b8a440a23f608661c5`.
The cold job completed in `16m48s`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `11:13:05Z` to `11:27:03Z`, completed
8,500 jobs and emitted no warning or error in the new target. The audit ended
at `11:27:06Z`. Both stages exited zero, and all five audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9060791193`, named
`flat-qprime-alias-fibre-dictionary-2a99a8997763597e7faac87c6455163c3df3ec99`,
has GitHub digest
`348177eb8b058a2f31c652990cc9332af7cfc81f5309475137e582051fe32a0d`.
Its deterministic inner archive re-hashed on Windows to
`ce1ec18781b8f1e3fdb121b831ae31f07a54edef3be37e56a6ec9f6eca446cf3`;
all 13 internal manifest entries matched.

The dictionary contains no free enumeration. Euclidean division identifies
the fixed coarse-alias fibre in `FinBox d (M*N')` with `FinBox d M`; the
coordinate formula retains the literal reconstruction
`fine = ell + N' * quotient`. A second canonical equivalence translates the
quotient to the centered half-open interval beginning at `-floor(M/2)`, and
the product equivalence lands in `CMP89Eq246AliasIndex d M 1`. Thus the even
endpoint convention is the one printed in CMP89 (2.45), not an arbitrary
congruence representative.

This brick identifies carriers only. The signed amplitude momentum still has
to be transported to the CMP89 alias momentum using its proved `2*pi*M`
period before the weighted adjoint and rank-one `Q'^*Q'` matrix can be
identified. Inverse uniqueness and regional transport remain open. Physical
`B0`, window 15 and every terminal field remain open. Counters stay exactly
`20/41`, `TermSource = 0`. Failed diagnostics `31381194800`, `31381581934`
and `31381866244` preserve the four initial elaboration failures, the reduced
single `mod` failure and the opaque-product-coordinate failure respectively.
Restored diagnostic PASS `31382114494` did not seal; only the cold run above
retires the two PRE-VALIDATION marks.

### Step 7.5cxlii signed fine momentum to the printed CMP89 alias momentum (SEALED; weighted-adjoint matrix open)

Exact source checkpoint `5225ae39da3458a93aba34f79c045971f7922d24`
passed cold GitHub Actions run
[`31386205166`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31386205166)
with workflow checkpoint `e12cd097c3eb2688e0c51e32035121a88a0fe4d4`.
The cold job completed in `23m41s`; restoration and saving of `.lake/build`
were both skipped. The focal ran from `12:04:55Z` to `12:26:35Z`, completed
8,530 jobs and emitted no warning or error in the new target. The audit ended
at `12:26:41Z`. Both stages exited zero, and all eight audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9062479430`, named
`flat-qprime-signed-alias-momentum-dictionary-5225ae39da3458a93aba34f79c045971f7922d24`,
has GitHub digest
`af5c4d89f46faaee0da69fc1060131398439af9c16d34c70e04532b7147b9b00`.
Its deterministic inner archive re-hashed on Windows to
`4b82f8728f017ad2fb74be1e9fd307cd0667521d2efae06b152ff5256241e16b`;
all 13 internal manifest entries matched.

The order-preserving carrier enumeration of Step 7.5cxli is deliberately not
used as a momentum identity. The physical one-block amplitude is evaluated at
`-M * p_fine`, so the new equivalence sends the quotient residue `q` to the
unique centered representative of `-q mod M`. It is constructed through the
explicit affine involution `x |-> -x - lower` on `ZMod M`. The module proves
that the resulting printed alias integer plus `q` is divisible by `M`, hence
the physical amplitude momentum differs from the CMP89 alias momentum by an
internally constructed integer multiple of the exact `2*pi*M` period in each
coordinate.

Column and opposite-momentum row transports are proved separately. Thus no
abstract self-adjointness or shared use of the word "row" changes the
orientation, and no pointwise equality of different reciprocal
representatives is asserted. The next source-facing brick is the literal
diagonal-plus-rank-one matrix identity for the weighted adjoint and
`Q'^*Q'` on this signed alias fibre. Inverse uniqueness and regional transport
remain open. Physical `B0`, window 15 and every terminal field remain open.
Counters stay exactly `20/41`, `TermSource = 0`. Failed diagnostics
`31384293486`, `31384589759`, `31384920151`, `31385271471` and `31385586958`
preserve the coercion, carrier-normalization and elaboration failures.
Restored diagnostic PASS `31385953304` did not seal; only the cold run above
retires PRE-VALIDATION.

### Step 7.5cxliii physical diagonal-plus-rank-one alias precision matrix (SEALED; active-region CLM and inverse open)

Exact source checkpoint `e77a9ba120a621298f800db1dd73c4c75dec8d62`
passed cold GitHub Actions run
[`31390994217`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31390994217)
with workflow checkpoint `b5e940837dd4a09394e0010bfb0194b428e3b499`.
Restoration and saving of `.lake/build` were both skipped. The focal ran from
`13:08:42Z` to `13:30:44Z`, completed 8,533 jobs, and emitted no warning or
error in the new target. The audit ended at `13:30:52Z`; both stages exited
zero and all seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The producer keeps the two physical momentum orientations literal. The
opposite-momentum entire average performs fibre analysis, the direct-momentum
factor performs synthesis, and their matrix action is proved to be exactly
synthesis after analysis. The physical diagonal is the rescaled periodic
stencil with its single `M^2` spacing conversion and mass term. The signed
alias dictionary of Step 7.5cxlii transports the diagonal and the two rank-one
axes separately; reindexing both axes yields the printed CMP89 entire
diagonal-plus-rank-one precision matrix. No abstract self-adjointness exchanges
the row and column factors, and the diagonal and rank-one coefficients remain
separate.

This is the finite flat Fourier-fibre matrix identity. It does not yet identify
the active-region transported real/complex CLM with the fibre
analysis/synthesis, construct its weighted adjoint, prove inverse uniqueness,
or transport the inverse to the regional Green operator. Physical `B0`, window
15 and every terminal field remain open. Counters stay exactly `20/41`,
`TermSource = 0`. Failed diagnostics `31389151982`, `31389531313`,
`31389925909` and `31390252630` preserve only elaborational normalization
repairs. Restored diagnostic PASS `31390748590` did not seal; only the cold run
above retires PRE-VALIDATION.

### Step 7.5cxliv literal flat physical contour transport (SEALED; interacting transport and regional Green open)

Exact source checkpoint `00177e508cfb22e302b7487a82bce001f9631aee`
passed cold GitHub Actions run
[`31395397728`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31395397728)
with workflow checkpoint `4e2e3e4f8f75348155bd82f3287024166fca3dda`.
The cold job ran for `17m44s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `13:57:30Z` to `14:13:11Z`, completed 8,428
jobs and emitted no warning or error in the new target. The audit ended at
`14:13:20Z`. Both stages exited zero and all seven audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9066008436`, named
`flat-physical-transport-00177e508cfb22e302b7487a82bce001f9631aee`,
has GitHub digest
`53a273c402b3d19e3be1e38854a5e634adccb774f97a566c5282c183215b3f72`.
Its deterministic inner archive re-hashed on Windows to
`7d478de3cab99843e1fb99c2d20251d1d7d6b546ca0f3a5b2bf6ede40f36e625`;
all 13 internal manifest entries matched.

The physical source average is not supplied with an arbitrary transport.
The new producer constructs the literal flat gauge configuration, proves
every ordered Wilson line and contour holonomy equal to one, and therefore
identifies the source-constructed adjoint transport with the identity. Its
two consumers then reduce the actual one-step physical average to the
source-normalized `M^-d` block sum and the actual source weighted adjoint to
unit-coefficient synthesis. No transport family or normalization is supplied
as data.

This is the exact flat-background specialization on an arbitrary
block-saturated active region. It does not identify the interacting contour
transport with the flat one, construct the physical complexified Fourier
transform, identify the active-region CLM with the sealed fibre matrix,
construct its inverse, or transport an inverse to the regional Green
operator. Physical `B0`, window 15 and every terminal field remain open.
Counters stay exactly `20/41`, `TermSource = 0`. Failed diagnostics
`31394121111` and `31394732916` preserve respectively the explicit-instance
and equivalence-extensionality/identity-normalization repairs. Diagnostic PASS
`31395156202` restored the graph and did not seal; only the cold run above
retires the PRE-VALIDATION mark.

### Step 7.5cxlv active flat physical complex-mode action (SEALED; weighted adjoint and inverse open)

Exact source checkpoint `94a93d24e8dcad9314a8e1446a1bad0119acc7e0`
passed cold GitHub Actions run
[`31405153522`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31405153522)
with workflow checkpoint `a1f4d9cb1c67e5a3188a4051baf973f2f7b94921`.
The cold job ran for `23m26s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `15:46:05Z` to `16:07:15Z`, completed 8,490
jobs and emitted no warning or error in the new target. The audit ended at
`16:07:25Z`. Both stages exited zero and all ten audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9070103679`, named
`flat-physical-complex-mode-94a93d24e8dcad9314a8e1446a1bad0119acc7e0`,
has GitHub digest
`4ffa9aebf84ac56ad615aeed57b54ee1958184ca463b4882c6aa8b5e42f4f278`.
Its deterministic inner archive re-hashed on Windows to
`f350795c50a94d1a2a0e56f562b544ecd4c068e1d67bceaa139e5c16e19e7b40`;
all 13 internal manifest entries matched.

The producer constructs pointwise complexification on the actual active
zero-cochain, constructs the source-normalized complex average with identity
flat transport, and proves that this average commutes with complexification
of the literal physical flat average. Restricting an internally constructed
complex Fourier mode to the active region then gives the exact coarse-alias
mode action, using the canonical block-offset equivalence and the sealed
one-block amplitude. No Fourier family, transport family or reciprocal
enumeration is supplied by the caller.

This is the active-region flat average action, not the source weighted-adjoint
action on Fourier coefficients. Interacting transport, a global Fourier
equivalence, weighted-adjoint analysis/synthesis, inverse uniqueness and
regional Green transport remain open. Physical `B0`, window 15 and every
terminal field remain open. Counters stay exactly `20/41`, `TermSource = 0`.
Failed diagnostics `31398057183`, `31398178152`, `31398683698`,
`31399256447` and `31402382641` preserve respectively the cache-key,
complexification/elaboration, dependent-extensionality, definitional-sum and
docstring-scope failures. Diagnostic PASSes `31399586719`, `31399873331` and
`31404901940` did not seal: the first two predate removal of the target's own
warning, and the last restored the project graph. Only the cold run above
retires PRE-VALIDATION.

### Step 7.5cxlvi flat physical complex weighted adjoint (SEALED; Fourier column and inverse open)

Exact source checkpoint `85763428444a29a64dd05ba1369ed493fe7f6c91`
passed cold GitHub Actions run
[`31408636358`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31408636358)
with workflow checkpoint `bf2b4f8746ff615c3f21e0752bcbc3a4ccbc6d24`.
The cold job ran for `24m00s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `16:25:47Z` to `16:46:48Z`, completed 8,491
jobs and emitted no warning or error in the new target. The audit ended at
`16:46:56Z`. Both stages exited zero and all six audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9071431702`, named
`flat-physical-complex-weighted-adjoint-85763428444a29a64dd05ba1369ed493fe7f6c91`,
has GitHub digest
`410dbbc1d4b865ab8957911c4004a526fb24dd5303a95da849492a91cc85cb3a`.
Its deterministic inner archive re-hashed on Windows to
`ef3e5b8935db046b99b8d6d34fc4b106b3341a5cd336d1a9e6ed2db099f093d2`;
all 13 internal manifest entries matched.

The producer constructs the source weighted adjoint on the explicit complex
physical fibre with coefficient one and the sealed identity flat transport.
It proves pointwise commutation with complexification of the literal physical
weighted adjoint. Applied to a restricted coarse complex Fourier mode, it is
exactly the fine-region field obtained by evaluating that mode at the owner
block of each fine site. No adjoint family or synthesized field is supplied
as caller data.

This endpoint is pointwise synthesis, not a theorem about fine Fourier
coefficients. The direct-momentum column on a fixed reciprocal fibre still
requires a global Fourier equivalence and its normalization. Interacting
transport, inverse uniqueness and regional Green transport remain open.
Physical `B0`, window 15 and every terminal field remain open. Counters stay
exactly `20/41`, `TermSource = 0`. Failed diagnostic `31407924638` preserves
the identity-transport normalization, complexification exposure and command
scope repairs. Restored diagnostic PASS `31408296172` did not seal; only the
cold run above retires PRE-VALIDATION.

### Step 7.5cxlvii multidimensional flat DFT convention (SEALED; FinBox and physical-fibre adapters open)

Exact source checkpoint `a9389e1086cb426cb4eae4f35775b228b6090b19`
passed cold GitHub Actions run
[`31418790263`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31418790263)
with workflow checkpoint `afbb314f65d16f4120403565dbea7f8225572a9d`.
The cold job ran for `26m18s`; restoration and saving of `.lake/build` were
both skipped. The focal ran from `18:28:25Z` to `18:49:10Z`, completed 8,477
jobs and emitted no warning or error in the new target. The audit ended at
`18:49:22Z`. Both stages exited zero and all fourteen audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Artifact `9075311781`, named
`flat-multidimensional-dft-a9389e1086cb426cb4eae4f35775b228b6090b19`,
has GitHub digest
`95ba040d565aecc76aca595598e263421f7621343f0a9224c62e5e24966ebdbb`.
Its deterministic inner archive re-hashed on Windows to
`816c7772f013ceb82dde73ec21cd8269dd6ae3a221d30c1dc1e7167914e62b3e`;
all 13 internal manifest entries matched.

The producer fixes the periodic scalar Fourier convention on
`Fin d -> ZMod N`: the forward transform uses the negative product character,
the inverse uses the positive character with the literal normalization
`((N : ℂ)^d)⁻¹`, and product orthogonality proves both inversion directions.
The two maps are bundled as a complex-linear equivalence. Neither the sign
nor the normalization is supplied by a caller.

This is not yet the direct-momentum Fourier column of the physical weighted
adjoint. The adapters to `FinBox`, active-region restrictions and the
`SUNLieComplexCoord` fibre remain open, as do interacting transport, inverse
uniqueness and regional Green transport. Physical `B0`, window 15 and every
terminal field remain open. Counters stay exactly `20/41`, `TermSource = 0`.
Failed diagnostics `31411577995`, `31411892487`, `31412274838`, `31413438061`,
`31413805233`, `31414105657`, `31414569549` and `31414881088` preserve the
interface, character-negation, finite-sum and scalar-linearity repairs.
Runs `31412567515` and `31415184980` were cancelled as dependency-materialization
incidents before Lean. Restored diagnostic PASS `31416032381` did not seal.
Cold PASS `31416346641` retained a target linter warning and therefore did not
seal. Diagnostic PASS `31418530925` was warning-free but restored the graph;
only the final cold run above retires PRE-VALIDATION.

### Step 7.5cxlviii exact FinBox DFT transport (SEALED; physical-fibre adapter and direct column open)

Exact source checkpoint `9e1908ee7e5734dadfeae392443673d0bdbb5942`
passed cold GitHub Actions run
[`31421947998`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31421947998)
with workflow checkpoint `3a8002de2b6ef18ecdc88f956dda23b699b3b1db`.
The cold job ran for `27m26s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `19:07:30Z`; the focal
then built 8,478 jobs through `19:27:58Z`, and the audit ended at
`19:28:06Z`. Both stages exited zero. The first three of the eight audited
declarations use `[propext, Quot.sound]`; the remaining five use exactly
`[propext, Classical.choice, Quot.sound]`. The new target emitted no warning
or error.

Artifact `9076527091`, named
`flat-finbox-dft-9e1908ee7e5734dadfeae392443673d0bdbb5942`, has GitHub digest
`d499c40249f2b29ba6924e9a5456cdd1799d70a05e0cdfb1cd4ad9e78941f40f`.
Its deterministic inner archive re-hashed on Windows to
`778109ad2a5ce688f3c2e14dd221d4a944a8b11982768974355ec38484731619`;
all 13 internal manifest entries matched.

The producer constructs the literal equivalence from `FinBox d N` to the
sealed additive box `Fin d -> ZMod N`, transports the negative-character
forward DFT and normalized positive-character inverse through that
equivalence, proves both inverse laws and exposes the resulting complex-linear
equivalence. The character convention and normalization are inherited from
the sealed scalar DFT rather than supplied again by a caller.

This is not yet a DFT on the physical `SUNLieComplexCoord` fibre, an
active-region restriction or the direct-momentum column of the source
weighted adjoint. Interacting transport, inverse uniqueness, regional Green
transport and the physical `B0` remain open. Window 15 is still compatible
but not attained. Counters stay exactly `20/41`, `TermSource = 0`. Restored
diagnostic PASS `31421681555` did not seal; only the cold run above retires
PRE-VALIDATION from the two FinBox modules.

### Step 7.5cxlix full-box physical-fibre DFT and modal delta (SEALED; active weighted-adjoint column open)

Exact source checkpoint `0aa11e7afa4e4f1f9ca4a3e719e0535ed6165c39`
passed cold GitHub Actions run
[`31425137141`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31425137141)
with workflow checkpoint `1eed0187829697715c28dc7ebd60e13440569b76`.
The cold job ran for `19m13s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `19:41:21Z`; the focal
built 8,490 jobs from then through `19:58:12Z`, and the audit ended at
`19:58:21Z`. Both stages exited zero. All twelve audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`, and the new target emitted
no warning or error.

Artifact `9077463725`, named
`flat-physical-fibre-dft-0aa11e7afa4e4f1f9ca4a3e719e0535ed6165c39`,
has GitHub digest
`86096279162087f20836545a3fb060b555f816fedd5939f6184deaa98f4f0ae6`.
Its deterministic inner archive re-hashed on Windows to
`28ef81cc1563ec366fc3b6f5e2d313a36282bdc14d911a3e01d6a16748d9f957`;
all 13 internal manifest entries matched.

The producer identifies the existing physical Fourier mode with the sealed
product character, proves its exact scalar delta column, and applies the
full-box DFT coordinatewise to `SUNLieComplexCoord`. The coordinatewise
inverse laws are proved internally and bundled as a complex-linear
equivalence. One physical complex-fibre mode therefore transforms to the
literal coefficient `(N : ℂ)^d` at its unique momentum and zero elsewhere;
neither a Fourier family nor its inverse is caller data.

This does not yet restrict the transform to an active region or compute the
fine reciprocal-alias column of the source weighted adjoint. That next
column must retain the negative-character orientation and the condition
`coarseAlias(k) = ell`; it is not a single fine Fourier mode. Interacting
transport, inverse uniqueness, regional Green transport and physical `B0`
remain open. Window 15 remains compatible but unattained. Counters stay
exactly `20/41`, `TermSource = 0`. Restored diagnostic PASS `31424842327`
did not seal; only the cold run above retires PRE-VALIDATION.

### Step 7.5cl scalar reciprocal-fibre column of the flat weighted adjoint (SEALED; physical-fibre lift open)

Exact source checkpoint `26e9ee6f5ce3e1251d50cd862356350f6ff5538d`
passed cold GitHub Actions run
[`31431328313`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31431328313)
with workflow checkpoint `168148a6de750f7d5da88fb63d00531114dceb3e`.
The cold job ran for `22m56s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `20:56:32Z`; the focal
completed from then through `21:17:33Z`, and the audit ended at `21:17:40Z`.
Both stages exited zero. The first two of seven audited declarations use
`[propext, Quot.sound]`; the other five use exactly
`[propext, Classical.choice, Quot.sound]`. The axiom blacklist was empty.

Artifact `9079913123`, named
`flat-weighted-adjoint-scalar-column-26e9ee6f5ce3e1251d50cd862356350f6ff5538d`,
has GitHub digest
`62610c78a3b3d70508a3f8ca8dc51bcb0471b3cbd11201325028ef4f26c8b933`.
Its deterministic inner archive re-hashed on Windows to
`9a013f80337396a64bd16f3e6366fcb316120b6b91238bee48bde0a515e85157`;
all 13 internal manifest entries matched.

The producer transports periodic momentum negation through the sealed
`FinBox`--`ZMod` equivalence rather than identifying half-open real
representatives. It rewrites the literal forward DFT as a sum against that
negative mode, reindexes the complete fine box by owner blocks, consumes the
sealed one-block amplitude and obtains support exactly on
`coarseAlias(k) = ell`. Removing the source block weight by its proved
`M^d` normalization leaves the complete fine-volume coefficient and the
one-block entire amplitude at the literal periodic negative momentum.

This is the scalar column only. It does not supply a physical Lie-fibre
vector, replace the active weighted adjoint by a free field, identify flat
and interacting transport, invert the precision, restrict to a regional
Dirichlet carrier or produce the physical `B0`. Window 15 remains compatible
but unattained. Counters stay exactly `20/41`, `TermSource = 0`. Failed
diagnostics `31429164908` and `31430000991` preserve only equivalence,
instance and definitional-reduction repairs. Restored diagnostic PASS
`31431068711` did not seal; only the cold run above retires PRE-VALIDATION.

### Step 7.5cli physical-fibre reciprocal column of the flat weighted adjoint (SEALED; interacting and regional transport open)

Exact source checkpoint `ad78686dbff42e180c82480e1342b3b37eaa47f0`
passed cold GitHub Actions run
[`31434869611`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31434869611)
with workflow checkpoint `d682e8b23a1dd04f4ecb86df95c3e78ec1821ec2`.
The cold job ran for `25m11s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `21:43:33Z`; the focal
exited zero at `22:04:48Z` and the audit exited zero at `22:04:56Z`. All six
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`;
the axiom blacklist was empty.

Artifact `9081263523`, named
`flat-weighted-adjoint-physical-column-ad78686dbff42e180c82480e1342b3b37eaa47f0`,
has GitHub digest
`776f1f8820055f7b9cc4350edaca61bc2f12f001a12bc365cad1e6830852b71c`.
Its deterministic inner archive re-hashed on Windows to
`81b6146d8e92b114688b6c512e3cf0b2af88119e09d16920bac16c84eccbc63e`;
all 13 internal manifest entries matched.

The producer specializes the literal active-region flat complex weighted
adjoint to the full fine box and applies it to one restricted coarse Fourier
mode. The scalar owner-block pullback is lifted coordinatewise to the
`SUNLieComplexCoord` fibre. Its full-box DFT is supported exactly on
`coarseAlias(k) = ell`, with the complete fine-volume coefficient and the
literal one-block entire amplitude at periodic negative momentum. The fine
field is constructed internally; it is not accepted as caller data.

This remains the flat, full-box physical-fibre column. It does not identify
flat and interacting transport, invert the physical precision, restrict to a
regional Dirichlet carrier or produce the physical `B0`. Window 15 remains
compatible but unattained. Counters stay exactly `20/41`, `TermSource = 0`.
Failed diagnostic `31433709204` preserves the already-closed-goal elaboration
error; restored diagnostic PASS `31434412694` did not seal. Only the cold run
above retires PRE-VALIDATION.

### Step 7.5clii exact Fourier orientation of the flat physical weighted adjoint (SEALED; inverse, interacting and regional transport open)

Exact source checkpoint `7cc2a9d7e36aad31e65712ac5bd27189131b8916`
passed cold GitHub Actions run
[`31438216272`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31438216272)
with workflow checkpoint `d73dd4f88f39f4434178168d2a51fc23d77c3052`.
The cold job ran for `23m39s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `22:27:00Z`; the focal
exited zero at `22:48:47Z` and the audit exited zero at `22:48:54Z`. All three
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`;
the axiom blacklist was empty.

Artifact `9082415438`, named
`flat-weighted-adjoint-fourier-orientation-7cc2a9d7e36aad31e65712ac5bd27189131b8916`,
has GitHub digest
`ebf2f60d14e8b6f0afd23b5fa8ec3c1a5bdb4f15fac34c70ff44d47982ce1935`.
Its deterministic inner archive re-hashed on Windows to
`bdeda74aa1c7e5bd6f28d80c152369ae498301d9836339448db4264236e43218`;
all 13 internal manifest entries matched.

The producer proves that literal `ZMod` Fourier negation changes the physical
one-block amplitude momentum by an internally constructed integer multiple
of the exact `2*pi*M` period. It then proves amplitude invariance under that
period and identifies the fixed-coarse-fibre DFT of the physical flat
weighted-adjoint column with the separately printed opposite-momentum alias
row. No abstract self-adjointness exchanges the two orientations.

This does not invert the alias matrix, identify flat and interacting
transport, restrict to a regional Dirichlet carrier or produce physical
`B0`. Window 15 remains compatible but unattained. Counters stay exactly
`20/41`, `TermSource = 0`. Failed diagnostic `31437612264` preserves the
cast-normalization failure; restored diagnostic PASS `31437959575` did not
seal. Only the cold run above retires PRE-VALIDATION.

### Step 7.5cliii transposed alias-fibre solution of CMP89 (2.47) (SEALED; central stabilization and physical specialization open)

Exact source checkpoint `bb8bd699814d7862cb476216d4188db6cc711ec9`
passed cold GitHub Actions run
[`31441217997`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31441217997)
with workflow checkpoint `7ae74776394d0d13fe01f0827b54c7f0ecc4f608`.
The cold job ran for `2m29s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `23:11:09Z`; the focal
exited zero at `23:11:46Z` and the audit exited zero at `23:11:49Z`. All three
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`;
the axiom blacklist was empty.

Artifact `9082955042`, named
`entire-alias-transpose-solution-bb8bd699814d7862cb476216d4188db6cc711ec9`,
has GitHub digest
`af7b7aca6c8e60cb1c659dfa9ff90200742965a55a37ab8cd3bd310dc0edcf6e`.
Its deterministic inner archive re-hashed on Windows to
`e1810796ebbeb308bedb5c638521ec00436e154f3a443dc393a6a78bf0fa69ee`;
all 13 internal manifest entries matched.

The module proves that the DFT convention fixed in Step 7.5clii makes the
source equation use the transpose of the printed
`diag(Delta) + a * column * row` matrix. Its direct-momentum column is then
inside the contraction and its opposite-momentum row is the output source,
so the internally constructed solution has exactly the printed denominator
`1 + a * sum column*row/Delta`. No abstract adjoint or arbitrary solution
family is supplied.

The theorem is deliberately restricted to the domain where the printed
quotients are defined. The central removable zero, its stabilized analytic
continuation, the physical fixed-fibre specialization, interacting/regional
transport and physical `B0` remain open. Window 15 remains compatible but
unattained. Counters stay exactly `20/41`, `TermSource = 0`. Failed diagnostic
`31440675278` preserves the transpose/abbreviation normalization errors;
restored diagnostic PASS `31441006236` did not seal. Only the cold run above
retires PRE-VALIDATION.

### Step 7.5cliv physical fixed-fibre specialization of the transposed CMP89 (2.47) solution (SEALED; central stabilization and literal full-box precision action open)

Exact source checkpoint `62ce05f17719fa5946dbbc80993c9ffd288f2ec1`
passed cold GitHub Actions run
[`31443022370`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31443022370)
with workflow checkpoint `7d365bde8871578bd76424dabdc832ad80871e59`.
Restoration and saving of `.lake/build` were both skipped. The focal ran from
`23:38:50Z` to `00:01:28Z`, completed `8,535` jobs and exited zero; the audit
exited zero at `00:01:33Z`. Both audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist was empty and
the new modules emitted no linter warning.

Artifact `9084019035`, named
`physical-alias-transpose-solution-62ce05f17719fa5946dbbc80993c9ffd288f2ec1`,
has GitHub digest
`4e384aa9137a7fd3333e62f75c1e1ea982d3de33297d80dcfc2adb07cdaed36b`.
Its deterministic inner archive re-hashed on Windows to
`614eee6a6258d468130720972ec29166495315828a5b3fadbc844aa3b3d24f60`;
all 13 internal manifest entries matched.

The source pulls the internally constructed transposed solution back through
the already sealed signed equivalence between the literal fixed physical
coarse fibre and the depth-one CMP89 alias carrier. Entrywise precision,
fine-symbol and opposite-momentum row dictionaries are consumed inside the
proof, and the finite sum is transported by the equivalence rather than by a
free enumeration. Thus the transpose of the literal physical fibre matrix
solves the literal physical opposite-momentum source on the nonsingular
domain of the printed quotients.

This does not yet identify that matrix action with the DFT of the literal
full-box complex precision, stabilize the removable central zero, construct
an inverse CLM, transport to the interacting/regional Green operator or
produce physical `B0`. Window 15 remains compatible but unattained. Counters
stay exactly `20/41`, `TermSource = 0`. Failed diagnostics `31442342886` and
`31442580969` preserve the pinned-index and equivalence-normalization errors;
restored diagnostic PASS `31442806454` did not seal. Only the cold run above
retires PRE-VALIDATION.

### Step 7.5clv literal full-box precision mode action and physical DFT column (SEALED; arbitrary coefficient vectors and central stabilization open)

Exact source checkpoint `aeeaf38cd0fd31c7b0e5a71e35129191b50b312e`
passed cold GitHub Actions run
[`31448164862`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31448164862)
with workflow checkpoint `7abd190cead5377d1e09081abd943106c8b997c7`.
Restoration and saving of `.lake/build` were both skipped. The focal ran from
`01:06:35Z` to `01:29:46Z`, completed `8,543` jobs and exited zero; the audit
exited zero at `01:29:54Z`. All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist was empty and
the new module emitted no linter warning.

Artifact `9085767466`, named
`flat-full-complex-precision-mode-action-aeeaf38cd0fd31c7b0e5a71e35129191b50b312e`,
has GitHub digest
`19db379b4da0f57c4a90a7fdd6e64a64496863c95fba2136dfca1d428116ec79`.
Its deterministic inner archive re-hashed on Windows to
`c70f76e18ce440e13ac365f46bf948e44083e556458c6e92b1f84d8266cf3faa`;
all 13 internal manifest entries matched.

The source constructs the literal full-box `Q'^*Q'` by composing the sealed
source-normalized flat average with its coefficient-one weighted adjoint. It
then assembles the printed flat precision as the sum of the `M^2`-scaled flat
stencil, the separate scalar mass-squared term and `a Q'^*Q'`. On one physical
Fourier mode its exact forward DFT is the fine-volume multiple of one column
of the transpose of the sealed physical alias precision matrix. The transpose
and opposite-momentum row are inherited from the literal DFT/weighted-adjoint
orientation; no synthetic Fourier operator or abstract self-adjointness is
substituted.

This does not yet lift the column equality to an arbitrary fixed-fibre
coefficient vector, construct the physical solution field, stabilize the
central removable zero, build an inverse CLM, identify the stabilized Fourier
kernel with `G Q'^*`, transport to the interacting/regional operator or
produce physical `B0`. Window 15 remains compatible but unattained. Counters
stay exactly `20/41`, `TermSource = 0`. Failed diagnostics `31445364521`,
`31445590852` and `31445847597` preserve the coarse-alias, nominal-DFT and
folded-rank-one elaboration boundaries. Warm passes `31446095141` and
`31447893374` did not seal. Cold PASS `31446282022` is retained as superseded
evidence because its source emitted one unused-instance linter warning; only
the warning-free cold run above retires PRE-VALIDATION.

### Step 7.5clw arbitrary fixed-fibre precision action (SEALED; physical solution field and central stabilization open)

Exact source checkpoint `35f755aa97f098893ee44b7f8a286dd34f6c0a28`
passed cold GitHub Actions run
[`31453744491`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31453744491)
with workflow checkpoint `f1796a2a9c0ebec6a6c8e4f3583d79130fafb7c7`.
Restoration and saving of `.lake/build` were both skipped. The focal ran from
`02:55:50Z` to `03:19:17Z`, completed `8,544` jobs and exited zero; the audit
exited zero at `03:19:25Z`. All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and the explicit
new-module warning gate were both empty.

Artifact `9087703119`, named
`flat-full-complex-precision-fibre-action-35f755aa97f098893ee44b7f8a286dd34f6c0a28`,
has GitHub digest
`570edcc665ec24d38dd4a951999e75529e5f828e7f5cae283db8a96013ba91e1`.
Its deterministic inner archive re-hashed on Windows to
`bb9e2a540618b643f53fe699dde06eee5e2f74cf569534de10dc58b9126d0f9b`;
all 13 internal manifest entries matched.

The source extends one fixed reciprocal-fibre coefficient vector by zero to
the literal full momentum box and reconstructs its physical field with the
sealed inverse DFT. It proves the exact finite Fourier-mode expansion with the
inverse fine-volume normalization, packages the literal full-box precision as
an additive map and derives its arbitrary-vector DFT action as the transpose
physical alias matrix applied entrywise. The forward fine-volume factor and
inverse-transform normalization cancel internally; no synthetic Fourier
operator or free matrix action is introduced.

This does not yet construct the physical particular solution. That next brick
must scale the sealed transpose solution by the fine volume, prove the output
vanishes off the chosen reciprocal fibre and use DFT injectivity to obtain the
literal field equation. The central removable zero, inverse CLM,
stabilized-kernel dictionary, interacting/regional transport and physical
`B0` remain open. Window 15 remains compatible but unattained. Counters stay
exactly `20/41`, `TermSource = 0`. Failed diagnostics `31450180972`,
`31450508511`, `31450771159`, `31451005213`, `31451348876`, `31451551123`
and `31451740889` preserve the elaboration boundary; warm PASSes
`31451946285` and `31453542148` did not seal. Cold PASS `31452112604` is
retained as superseded evidence because its source emitted one unused-section
warning; only the warning-free cold run above retires PRE-VALIDATION.

### Step 7.5clx flat physical particular solution (SEALED; central stabilization open)

Exact source checkpoint `30386cddaddb1a6ce4f65ae8fc9bcb3bc3ff74e7`
passed cold GitHub Actions run
[`31456409096`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31456409096)
with workflow checkpoint `aa7ca9413ba3aa26d2858689121ca6919e883cd5`.
Restoration and saving of `.lake/build` were both skipped. The focal ran from
`03:48:14Z` to `04:12:03Z`, completed `8,547` jobs and exited zero; the audit
exited zero at `04:12:12Z`. All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and explicit
new-module warning gate were both empty.

Artifact `9088657541`, named
`flat-full-complex-precision-particular-solution-30386cddaddb1a6ce4f65ae8fc9bcb3bc3ff74e7`,
has GitHub digest
`38d03a50e822fc45a8dc66893a35835197271e9504b80199d07d471622ea7db5`.
Its deterministic inner archive re-hashed on Windows to
`96162f69a3c1b30529708bb955b6f2a7e51d5f858aef9609ba1ad64a2278d41c`;
all 13 internal manifest entries matched.

The source multiplies the sealed transposed fixed-fibre solution by the
literal fine volume and reconstructs an actual physical field through the
sealed inverse DFT. It proves its selected-fibre coefficient exactly, proves
both the field and literal precision output vanish on every other reciprocal
fibre, and identifies the selected output with the coefficient-one physical
weighted-adjoint source. DFT injectivity then yields the literal full-box
field equation; no synthetic Fourier operator or supplied solution family is
introduced.

The theorem still lies on the nonsingular domain of the printed rational
formula. The central removable zero and its stabilized solution, inverse CLM,
stabilized-kernel dictionary, interacting/regional transport and physical
`B0` remain open. Window 15 remains compatible but unattained. Counters stay
exactly `20/41`, `TermSource = 0`. Failed diagnostics `31455562523`,
`31455788779` and `31456041784` preserve the PiLp-coordinate, proof-order and
delimiter boundaries; warm PASS `31456262055` was diagnostic only. Only the
cold run above retires PRE-VALIDATION.

### Step 7.5cly central-stabilized transposed alias solution (SEALED; physical specialization open)

Exact source checkpoint `5265c73db3ec71ffaca115e1993375312e327ced`
passed cold GitHub Actions run
[`31459140597`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31459140597)
with workflow checkpoint `0e6372ce7cc473520cb81f114663ca6fd3a334b6`.
The cold job ran for `2m49s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `04:40:57Z`; the focal ran
from `04:40:57Z` to `04:41:46Z`, completed `3,294` jobs and exited zero; the
audit exited zero at `04:41:51Z`. All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and explicit
new-module warning gate were both empty.

Artifact `9089187256`, named
`stabilized-alias-transpose-solution-5265c73db3ec71ffaca115e1993375312e327ced`,
has GitHub digest
`44416f8d0833951dcf8feffbe1b23fec971a3c792e61fc65a27436770dcc7a92`.
Its deterministic inner archive re-hashed on Windows to
`49043a6e409ebd8e77ae2dcaaaccaa6b771e9cc646fb82b0d713bf9e6a0cf264`;
all 13 internal manifest entries matched.

The source separates the zero reciprocal alias before solving the literal
diagonal-plus-rank-one system. The central coefficient divides only by the
sealed stabilized denominator; every noncentral coefficient keeps the
literal fine-symbol quotient. The resulting vector is proved internally to
solve the transposed entire alias matrix, requiring nonvanishing only of the
noncentral fine symbols and the stabilized denominator. In particular no
nonvanishing premise is imposed on the central fine symbol, and the
noncentral subtype sum is identified with the printed CMP89 sum without a
free enumeration.

This is still the generic alias system. Pullback through the signed physical
fibre dictionary, the stabilized full-box particular field, inverse CLM,
interacting/regional transport and uniform physical `B0` remain open. Window
15 remains compatible but unattained. Counters stay exactly `20/41`,
`TermSource = 0`. Failed diagnostics `31458140980`, `31458352861`,
`31458580334` and `31458776556`, plus warm diagnostic PASS `31458994322`,
remain preserved. Only the cold run above retires PRE-VALIDATION.

### Step 7.5clz physical central-stabilized alias pullback (SEALED; full-box realization open)

Exact source checkpoint `7895a4f1a4b494f4d1a6a45986a4a748fe126088`
passed cold GitHub Actions run
[`31460094418`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31460094418)
with workflow checkpoint `f3e8c312824fdf6ff641cd2afc2eb94b788c1610`.
The cold job ran for `22m33s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `04:59:23Z`; the focal ran
from `04:59:23Z` to `05:19:48Z`, completed `8,536` jobs and exited zero; the
audit exited zero at `05:19:53Z`. All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and explicit
new-module warning gate were both empty.

Artifact `9089857733`, named
`physical-stabilized-alias-transpose-solution-7895a4f1a4b494f4d1a6a45986a4a748fe126088`,
has GitHub digest
`1ca5374027c8f7ea4c21463cb1b87446b842fd14ed11da5e8bce5a6bd35c3bb3`.
The downloaded deterministic archive has SHA-256
`289996b3e88a2a390e93a4fba46a9030adf3330a71f13027b74151b5d86c5a32`,
and all 13 internal manifest entries matched.

The source constructs the physical central fine mode as the inverse image of
the printed zero alias under the sealed signed fibre equivalence and pulls
back the complete stabilized solution.  Entrywise matrix and momentum
dictionaries are consumed internally.  The transpose of the literal physical
alias precision matrix therefore sends this vector to the literal
opposite-momentum average row while requiring the fine symbol to be nonzero
only away from the constructed central mode.  No central fine-symbol
nonvanishing, free enumeration or supplied solution family is introduced.

This is the exact physical fixed-fibre matrix solution, not yet its full-box
inverse-DFT realization as `G Q'^*`.  That realization, inverse uniqueness,
interacting/regional transport and uniform physical `B0` remain open. Window
15 remains compatible but unattained. Counters stay exactly `20/41`,
`TermSource = 0`. Failed diagnostic `31459717734` and warm diagnostic PASS
`31459917125` remain preserved. Only the cold run above retires the two
PRE-VALIDATION marks.

### Step 7.5cma physical central-stabilized full-box particular solution (SEALED; arbitrary coarse source and inverse uniqueness open)

Exact source checkpoint `7844238067f840687cee61b5d4df510a21f1d30a`
passed cold GitHub Actions run
[`31462172984`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31462172984)
with workflow checkpoint `8cd64709ca4c5a6c0385f50147e1ffed923ec4bd`.
The cold job ran for `25m22s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `05:37:43Z`; the focal ran
from `05:37:43Z` to `06:01:12Z`, completed `8,550` jobs and exited zero; the
audit exited zero at `06:01:20Z`. All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and explicit
new-module warning gate were both empty.

Artifact `9090675377`, named
`stabilized-full-complex-precision-particular-solution-7844238067f840687cee61b5d4df510a21f1d30a`,
has GitHub digest
`fb5e0e5e4ec8dfc0de2f6aafbeaf7bac92d9e03f8d7ba393227be31c65288b71`.
The downloaded deterministic archive has SHA-256
`3f6e66a866bd8fa4da0c56635db8386971fbe438e63d48ff1b9eef37827f644e`,
and all 13 internal manifest entries matched.

The source multiplies the sealed physical central-stabilized alias vector by
the literal fine volume and reconstructs an actual full-box field with the
sealed inverse DFT. It proves the exact selected-fibre coefficient, zero DFT
off that reciprocal fibre for both the field and the precision output, and
the selected-fibre identity with the coefficient-one physical weighted
adjoint. DFT injectivity then gives the literal full-box equation
`K h_ell(v) = Q'^* phi_ell(v)`. The central fine symbol is never required to
be nonzero, and no solution family or synthetic inverse is supplied.

This is one coarse Fourier mode of `G Q'^*`, not yet the operator on an
arbitrary coarse field. The finite coarse-mode superposition, inverse CLM,
identification by inverse uniqueness with the generated physical covariance,
interacting/regional transport and uniform physical `B0` remain open. Window
15 remains compatible but unattained. Counters stay exactly `20/41`,
`TermSource = 0`. Warm diagnostic PASS `31461960444` remains preserved and
did not seal. Only the cold run above retires the two PRE-VALIDATION marks.

### Step 7.5cmb physical central-stabilized `G Q'^*` for an arbitrary coarse source (SEALED; inverse packaging and generated identification open)

Exact source checkpoint `cc191c62e5109a343dfaacb97a1b28697177d35d`
passed cold GitHub Actions run
[`31465224082`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31465224082)
with workflow checkpoint `801906660f41ec244346d38ca18bd37f9afe5f29`.
The cold job ran for `25m19s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `06:30:36Z`; the focal ran
from `06:30:36Z` to `06:53:50Z`, completed `8,551` jobs and exited zero; the
audit exited zero at `06:53:59Z`. All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and explicit
new-module warning gate were both empty.

Artifact `9091813779`, named
`stabilized-qprime-star-field-cc191c62e5109a343dfaacb97a1b28697177d35d`,
has GitHub digest
`2741476943f15506b98ffac1f027fd5ede1d3dcfea1338cc790f88d67e8f8114`.
The downloaded deterministic archive has SHA-256
`d288d18947b4ace9ec12d3d7d0d9a2484cd35c16fc409e88e497406993eaf1fa`,
and all 13 internal manifest entries matched.

The source proves the literal finite inverse-DFT expansion of every coarse
physical field, specializes the coefficient-one full-box weighted adjoint to
each sealed Fourier mode, and sums the internally constructed one-mode
particular solutions. Linearity of the literal precision and exact DFT
inversion then give the full-box equation `K H eta = Q'^* eta` for every
coarse source. No inverse operator, solution family or reconstruction
identity is supplied by the caller.

This seals the arbitrary-source particular field, not an inverse CLM. Linear
packaging, identification by inverse uniqueness with the generated physical
covariance, interacting/regional transport and uniform physical `B0` remain
open. Window 15 remains compatible but unattained. Counters stay exactly
`20/41`, `TermSource = 0`. Failed diagnostics `31464394113` and
`31464695776`, and warm diagnostic PASS `31464995108`, remain preserved and
did not seal. Only the cold run above retires the two PRE-VALIDATION marks.

### Step 7.5cmc linearly packaged physical central-stabilized `G Q'^*` (SEALED; generated identification and regional transport open)

Exact source checkpoint `8e7a009f70627706391112cebfdbbbde622ca70a`
passed cold GitHub Actions run
[`31468954203`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31468954203)
with workflow checkpoint `2eceeece44d17a6dd5e6a83acda5820f0bc63b11`.
The cold job ran for `24m56s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `07:28:23Z`; the focal ran
from `07:28:23Z` to `07:51:22Z`, completed `8,552` jobs and exited zero; the
audit exited zero at `07:51:31Z`. All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and explicit
new-module warning gate were both empty.

Artifact `9093213008`, named
`stabilized-qprime-star-clm-8e7a009f70627706391112cebfdbbbde622ca70a`,
has GitHub digest
`6490e94eb4c31f666c1d984af212cc78f3fc9b730c5948adcf29bc4db4de72f2`.
The downloaded deterministic archive has SHA-256
`478770f5a6c0512a4c00d1189a1b18a1eb2a238f010d563c1742a54914c2b576`,
and all 13 internal manifest entries matched.

The source proves additivity and complex scalar linearity first for each
stabilized Fourier mode and then for the finite arbitrary-source
superposition. It packages the literal field `H = G Q'^*` as a linear map
and a continuous linear map and proves the bundled endpoint
`K (H eta) = Q'^* eta` internally.

This seals linear packaging of the arbitrary-source particular field, not a
constructed inverse `G`. Identification with the generated physical
covariance still requires matching the full carrier and operator: generated
parameters, trivial background, spacing normalization, the `Q'` tower,
mass/coupling conventions and real-to-complex extension must be made literal
before inverse uniqueness applies. Regional transport and uniform physical
`B0` also remain open. Window 15 remains compatible but unattained. Counters
stay exactly `20/41`, `TermSource = 0`. Failed diagnostics `31467608127`,
`31468200197` and `31468496923`, and warm diagnostic PASS `31468749704`,
remain preserved and did not seal. Only the cold run above retires the two
PRE-VALIDATION marks.

### Step 7.5cmk generated flat `Q'` recursive Fourier action (SEALED; terminal-collapse and stratum-precision dictionaries open)

Exact source checkpoint `97eb26010cf2aba4cae56e05ac94a32468688f4d`
passed cold GitHub Actions run
[`31508419658`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31508419658)
with workflow checkpoint `062f3f832120215d03739d4da8750bfca2282550`.
The job ran from `15:41:43Z` to `16:00:06Z` (`18m23s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`15:43:39Z`; the focal ran to `15:59:54Z`, completed `8,503` jobs and exited
zero. The audit ended at `16:00:01Z` and also exited zero. All seven audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9108666527`, named
`flat-generated-qprime-fourier-action-97eb26010cf2aba4cae56e05ac94a32468688f4d`,
has GitHub digest
`f40bd27626310ca8fbd821d6d3aca708edbc6987a0730de725e293f4da907e4b`.
The downloaded deterministic archive has SHA-256
`fece602a8f209e452b8f788af26ece0d4dd8d1907e8d5208afa28e5c979eae40`,
and all 13 internal manifest entries matched.

The sealed source proves complex homogeneity of the literal one-step average
and coefficient-one synthesis and lifts both facts through the complete typed
generated recursion. It then constructs, internally and by the same chain,
the product of one-step Fourier amplitudes and the terminal restricted mode
reached by the matching sequence of reciprocal aliases. The resulting exact
Fourier theorem retains every prefix region and alias.

This is not a collapse to one side-`M^depth` block, a global Fourier
equivalence, an identification of distinct CMP99 strata, a precision match,
an inverse or a regional Green estimate. Uniform physical `B0` and the
physical route to window 15 remain open. Live counters stay exactly `20/41`,
`TermSource = 0`. Failed diagnostics `31507440096` and `31507882118`, plus
warm PASS `31508177460`, remain preserved and did not seal. Only the cold run
above retires the two PRE-VALIDATION marks.

### Step 7.5cml generated flat counting/source-weighted adjoint dictionary (SEALED; terminal-collapse and stratum-precision dictionaries open)

Exact source checkpoint `cc62468f9afacc9c3266a9aedc2e0abf496c3bb6`
passed cold GitHub Actions run
[`31512759209`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31512759209)
with workflow checkpoint `753bfdcfb23642e407241cbf23f874545b17234d`.
The job ran from `16:30:41Z` to `17:02:10Z` (`31m29s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`16:37:36Z`; the focal ran to `17:01:50Z`, completed `8,482` jobs and exited
zero. The audit ended at `17:01:57Z` and also exited zero. All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9110856914`, named
`flat-generated-qprime-adjoint-dictionary-cc62468f9afacc9c3266a9aedc2e0abf496c3bb6`,
has GitHub digest
`d129177159ec93764b3a9c28ae0a3af3e789fb2e894e539b34796ca3b87882dc`.
The downloaded deterministic archive has SHA-256
`f1e682e724310dd8bb8c14c86c00a47e192eb24d695e6c2d32e637f69038b0e5`,
and all 13 internal manifest entries matched.

The sealed source proves that the counting-space adjoint of the literal flat
one-step average is exactly `M^{-d}` times the source-weighted coefficient-one
adjoint. It then lifts the conversion through the complete typed recursion:
the recursive counting adjoint is `(M^{-d})^depth` times the reverse weighted
adjoint recursion, and the same visible factor rewrites the exact generated
`Q'^* Q'` composition.

This is not a collapse to one side-`M^depth` block, an identification of CMP99
strata, a match with the separately reconstructed flat/full-complex precision,
an inverse, a Green estimate or a regional transport theorem. Uniform physical
`B0` and physical attainment of window 15 remain open. Counters stay exactly
`20/41`, `TermSource = 0`. Failed diagnostics `31511264192`, `31511622674` and
`31511987236`, plus content-PASS run `31512372910` whose packaging gate rejected
the then-visible new-module linter warning, remain preserved and did not seal.
Only the cold run above retires the two PRE-VALIDATION marks.

### Step 7.5cmi canonical flat generated `Q'/Q'^*` recursion (SEALED; printed one-block collapse and precision dictionaries open)

Exact source checkpoint `3857450a087721447f2456ba1a8e199565b1ed49`
passed cold GitHub Actions run
[`31500199257`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31500199257)
with workflow checkpoint `51e956f12036a624dc6875651913c36761e938c7`.
The job ran from `14:11:33Z` to `14:38:13Z` (`26m40s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`14:13:27Z`; the focal ran to `14:37:41Z`, completed `8,481` jobs and exited
zero. The audit ended at `14:38:08Z` and also exited zero. All sixteen audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9105674980`, named
`flat-generated-qprime-recursion-3857450a087721447f2456ba1a8e199565b1ed49`,
has GitHub digest
`a59a78c1728e89761ea846d5592568b30321e0e2661036de6746b4f123d4a3c4`.
The downloaded deterministic archive has SHA-256
`ee58f56f0a7c37c3b9036083060bead61675ff465e5b0203f259d6c0697f4400`,
and all 13 internal manifest entries matched.

The source constructs the identity transport on the literal flat background,
identifies both physical one-step maps with the explicit flat average and
coefficient-one weighted adjoint, and proves by induction on the typed active
region chain that the complete internally generated physical `Q'` and `Q'^*`
recursions equal their explicit flat recursions. Every hidden next background
is derived from physical Ubar. The two proof-data congruence lemmas make the
dependent radius-chain transport explicit; no operator family, successor
background or desired equality is caller data.

This seals the canonical typed flat recursion only. It does not collapse the
recursion to one printed block average of side `M^depth`, identify counting
with source-weighted adjoints, match the generated real precision with the
separately reconstructed flat complex precision, complexify it, or produce a
regional Green bound. Regional transport and uniform physical `B0` remain
open. Window 15 remains compatible but unattained. Counters remain exactly
`20/41`, `TermSource = 0`. Failed diagnostics `31494264301`, `31494624376`,
`31494990623`, `31495580310`, `31495961675`, `31496517462`, `31496912692`,
`31497266590`, `31497623352`, `31497972893`, `31498519455`, `31498980631`
and `31499483231`, plus warm diagnostic PASS `31499831474`, remain preserved
and did not seal. Only the cold run above retires the PRE-VALIDATION marks.

### Step 7.5cmj generated flat `Q'/Q'^*` complexification (SEALED; recursive Fourier and stratum-precision dictionaries open)

Exact source checkpoint `f9aa2a653b75b2225825bba6a93226477da37807`
passed cold GitHub Actions run
[`31504482851`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31504482851)
with workflow checkpoint `4fcc599e3622d3b419a58403913c45a924578df0`.
The job ran from `14:58:26Z` to `15:18:28Z` (`20m02s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`15:00:39Z`; the focal then ran to `15:18:15Z`, completed `8,502` jobs and
exited zero. The audit ended at `15:18:24Z` and also exited zero. All eight
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`;
the axiom blacklist and explicit two-module text and warning gates were empty.

Artifact `9107145977`, named
`flat-generated-qprime-complexification-f9aa2a653b75b2225825bba6a93226477da37807`,
has GitHub digest
`984f3d756f5d848edfce91a9face840728d9f23e516474ad3e2d06e256d3bfd4`.
The downloaded deterministic archive has SHA-256
`54eec107dd83a2439993646d34d0bd12b80678e5519db9d5878f6677e388951d`,
and all 13 internal manifest entries matched.

The source constructs the complete flat complex average and reverse
coefficient-one weighted-adjoint recursions internally on the same dependent
active-region chain as the sealed real recursion. It proves one-step
commutation with the canonical `matrixSUNAdjointModel Nc`, then proves by
induction that both complete recursions commute with pointwise
complexification. No complex operator family, intermediate background or
desired recursion equality is caller data.

This seals complexification of the typed per-prefix recursion, not an
identification of distinct CMP99 strata with one terminal block average. It
does not yet derive the recursive Fourier alias/amplitude action, collapse a
printed stratum, match the generated real precision with the separately
reconstructed full-complex precision, construct an inverse or produce a
regional Green bound. Regional transport and uniform physical `B0` remain
open. Window 15 remains compatible but unattained. Counters remain exactly
`20/41`, `TermSource = 0`. Failed diagnostic `31503784550` and warm diagnostic
PASS `31504207313` remain preserved and did not seal. Only the cold run above
retires the two PRE-VALIDATION marks.

### Step 7.5cmf canonical zero-radius normalized flat scale (SEALED; recursive flat tower and generated operator dictionaries open)

Exact source checkpoint `1f044aa0200ab73a9386df0a969e45d257db4f78`
passed cold GitHub Actions run
[`31481437430`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31481437430)
with workflow checkpoint `8dd1c35e235e300eb5a4424aad710645817f9096`.
The job ran from `10:15:58Z` to `10:34:29Z` (`18m31s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`10:17:44Z`; the focal ran to `10:34:18Z`, completed `8,430` jobs and exited
zero. The audit ended at `10:34:27Z` and also exited zero. All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text gate were empty.

Artifact `9097889525`, named
`flat-normalized-scale-1f044aa0200ab73a9386df0a969e45d257db4f78`, has
GitHub digest
`25a593b7b1984bc69a81264c0a87e6c65ef69513dc67d0366277bcf54329bbcb`.
The downloaded deterministic archive has SHA-256
`a2ca7484da309c5897e763d8d9a99ebf1bcab64ce87cfb09a862e8569ff4ec91`,
and all 13 internal manifest entries matched.

The sealed source proves positivity of the explicit no-winding threshold and
constructs the canonical source-normalized scale on a saturated active region
at literal fine radius zero. Linkwise smallness and no winding are generated
internally. Its physical-Ubar-produced `nextBackground` is then the literal
flat coarse gauge configuration by the preceding seal; neither the scale nor
the successor background is supplied by the caller. This is still one scale.
The zero-radius certificate chain, recursive flatness of the retained physical
tower, exact generated `Q'`, the counting-adjoint/weighted-adjoint spacing
factor, real precision matching and complexification remain explicit next
dictionaries. Regional transport and uniform physical `B0` remain open.
Window 15 remains compatible but unattained. Counters remain exactly `20/41`,
`TermSource = 0`. Warm diagnostic PASS `31480922329` remains preserved and did
not seal. Only the cold run above retires the two PRE-VALIDATION marks.

### Step 7.5cmg canonical generated flat retained tower (SEALED; intermediate-background and generated-operator dictionaries open)

Exact source checkpoint `cea77517466b91bd1b7fcb0c3a1d8292d158795e`
passed cold GitHub Actions run
[`31484384185`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31484384185)
with workflow checkpoint `c9c63c388518f317556332bddc95b1a4265b613d`.
The job ran from `10:56:16Z` to `11:16:07Z` (`19m51s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`10:58:03Z`; the focal ran to `11:15:55Z`, completed `8,447` jobs and exited
zero. The audit ended at `11:16:04Z` and also exited zero. All five audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9099057417`, named
`flat-retained-tower-cea77517466b91bd1b7fcb0c3a1d8292d158795e`, has GitHub
digest
`e6ceadb2688bb0911690e628e62916388777d7450ff9029ec7775c3251f29e16`.
The downloaded deterministic archive has SHA-256
`caef681c42bda31228039d33d4d4990f57d9d0112dfd7ce0736a48c41f69643b`,
and all 13 internal manifest entries matched.

The source proves that zero is an exact fixed point of the printed Ubar radius
recursion, constructs the complete proof-valued zero-radius chain from one
closed scalar budget, and feeds that chain plus the literal flat fine
background into the source recursion to construct the canonical generated
retained physical tower. Neither the chain nor a fine-smallness family is
caller data.

This seals existence of the actual recursively generated tower object, not an
identification of its hidden intermediate backgrounds with the flat
configuration. The exact generated `Q'` tower, the counting-adjoint versus
weighted-adjoint spacing factor, real precision matching and complexification
remain open dictionaries. Regional transport and uniform physical `B0` remain
open. Window 15 remains compatible but unattained. Counters remain exactly
`20/41`, `TermSource = 0`. Failed diagnostics `31483205444`, `31483629713` and
`31483956365`, plus warm diagnostic PASS `31484191821`, remain preserved and
did not seal. Only the cold run above retires the two PRE-VALIDATION marks.

### Step 7.5cmh retained terminal prefix equals the canonical generated `Q'` tower (SEALED; flat printed-operator dictionary open)

Exact source checkpoint `ee60acf0a1f8899ed3fc690771cb12a109cff7cf`
passed cold GitHub Actions run
[`31490868798`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31490868798)
with workflow checkpoint `5930c99f22c51e5772468243dc199714bbb2d1b9`.
The job ran from `12:22:09Z` to `12:42:27Z` (`20m18s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`12:23:53Z`; the focal ran to `12:42:08Z`, completed `8,464` jobs and exited
zero. The audit ended at `12:42:24Z` and also exited zero. All six audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9101583485`, named
`retained-generated-terminal-bridge-ee60acf0a1f8899ed3fc690771cb12a109cff7cf`,
has GitHub digest
`8c95112ee40fa90b5a6176ab35289c42deea9eaebacf5c30f9f9f05b8a0d41ea`.
The downloaded deterministic archive has SHA-256
`e5f00bc7dd9b3114f0eb1d2c1bd55cc0c7d8458192eac883c12e29850b428a5c`,
and all 13 internal manifest entries matched.

The source proves, by induction on the typed active-region chain, that the
last prefix of the recursively generated retained physical tower is exactly
the canonical generated `weightedQprimeTower`. Transport across the proved
regional equalities is internal, and the flat corollary uses the literal
zero-radius chain; no terminal operator family or identification equality is
supplied by the caller.

This seals the retained-to-generated terminal bridge only. It does not yet
identify the generated operator with the separately reconstructed flat
printed block average, expose the full canonical flat `Q'/Q'^*` recursion,
bridge counting adjoints to source-weighted adjoints, or finish real-precision
matching and complexification. Regional transport and uniform physical `B0`
remain open. Window 15 remains compatible but unattained. Counters remain
exactly `20/41`, `TermSource = 0`. Failed diagnostics `31487053514`,
`31487355478`, `31487710390`, `31488086415`, `31488392429`, `31488725784`,
`31489324526`, `31489622730`, `31489988724` and `31490350285`, plus warm
diagnostic PASS `31490585466`, remain preserved and did not seal. Only the
cold run above retires the PRE-VALIDATION mark.

### Step 7.5cmd flat full-complex inverse uniqueness (SEALED; generated physical dictionary open)

Exact source checkpoint `621a84bdd7a33ccb87f4bb02043d63cd52967ac4`
passed cold GitHub Actions run
[`31473379111`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31473379111)
with workflow checkpoint `7cc735a661d341bb1d5cb168a99106918c2ba336`.
The cold job ran for `23m06s`; restoration and saving of `.lake/build` were
both skipped. Dependency materialization ended at `08:30:40Z`; the focal ran
from `08:30:40Z` to `08:51:43Z`, completed `8,553` jobs and exited zero; the
audit exited zero at `08:51:52Z`. All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist and explicit
new-module text gate were both empty.

Artifact `9094887288`, named
`flat-precision-inverse-uniqueness-621a84bdd7a33ccb87f4bb02043d63cd52967ac4`,
has GitHub digest
`a631d09bc4d34db5c9aeef7b8606c8b5f38f1322a2431cea4126f91e6b2fcf22`.
The downloaded deterministic archive has SHA-256
`6368aa683db52e02e610b2f85cf5953535f8632568bd56475fe617f4e7254a44`,
and all 13 internal manifest entries matched.

The sealed source proves complex homogeneity of the literal flat full-box
precision and the coefficient-one physical weighted adjoint, packages both
as continuous complex-linear maps, and bundles `K H = Q'^*`. Given an
explicit left-inverse law `G K = id` for this same literal precision, inverse
uniqueness derives `H = G Q'^*` internally. The desired equality is not a
caller hypothesis.

This is an inverse-uniqueness bridge for the literal flat complex operator,
not yet its identification with the generated real physical tower. The next
dictionary must prove preservation of the flat background by physical Ubar,
collapse the generated `Q'` tower, expose the spacing ratio between Lean's
counting adjoint and the printed weighted adjoint, and match the real
precision before complexification. In particular the flat Fourier
coefficient is the generated mass multiplied by
`spacing^d / terminalSpacing^d`; it is not silently identified with the
generated mass. Regional/interacting transport and uniform physical `B0`
remain open. Window 15 remains compatible but unattained. Counters stay
exactly `20/41`, `TermSource = 0`. Failed diagnostics `31471917140`,
`31472242314`, `31472534664` and `31472872194`, plus warm diagnostic PASS
`31473137923`, remain preserved and did not seal. Only the cold run above
retires the two PRE-VALIDATION marks.

### Step 7.5cme physical Ubar preserves the literal flat background (SEALED; normalized one-scale and recursive tower dictionaries open)

Exact source checkpoint `bfb4c2a1802fc40933e8642cfbb839ba9fed939e`
passed cold GitHub Actions run
[`31478887310`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31478887310)
with workflow checkpoint `83a39a2250a4e882b8c2001716ea84f7be26f788`.
The job ran from `09:42:12Z` to `10:00:24Z` (`18m12s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`09:43:58Z`; the focal then ran to `10:00:10Z`, completed `8,429` jobs and
exited zero. The audit ended at `10:00:21Z` and also exited zero. All five
audited declarations use exactly `[propext, Classical.choice, Quot.sound]`;
the axiom blacklist and the explicit two-module text gate were empty.

Artifact `9096895600`, named
`flat-ubar-preservation-bfb4c2a1802fc40933e8642cfbb839ba9fed939e`, has
GitHub digest
`933a5cc258a7ad736058bab9e37daff66dd8346cacb0970335112d62af55a134`.
The downloaded deterministic archive has SHA-256
`10c777d08f46156b9533dfd779eef5a64da66962871a9bb21cb0f9c23a85de68`,
and all 13 internal manifest entries matched.

The sealed source proves, without a caller-supplied next background, that the
straight coarse transport of a flat fine gauge field is one, all four-contour
Ubar deviations are one, the finite special-unitary exponent is zero, and the
direct deviation-budget Ubar constructor returns the literal flat coarse
gauge configuration in both orientations. This is the exact one-scale Ubar
preservation statement; it does not yet construct the canonical normalized
scale at `epsilon = 0`, prove that the recursively generated tower remains
flat, identify the generated `Q'` tower or bridge Lean's counting adjoint to
the printed weighted adjoint. Those dictionaries remain explicit. Regional
transport and uniform physical `B0` remain open. Window 15 remains compatible
but unattained. Counters remain exactly `20/41`, `TermSource = 0`. Failed
diagnostics `31476670001`, `31477156542`, `31477467222`, `31477764120`,
`31478077838` and `31478373414`, plus warm diagnostic PASS `31478664898`,
remain preserved and did not seal. Only the cold run above retires the two
PRE-VALIDATION marks.

### Step 7.5cmm exact terminal-owner action and flat generated mass kernels (SEALED; terminal-block and stratum dictionaries open)

Exact source checkpoint `e781ba4a25bea54229a3679bc1af50536a42a2e2`
passed cold GitHub Actions run
[`31539934539`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31539934539)
with workflow checkpoint `694b241342b1e7465e80220d019276baed1b85f4`.
The job ran from `21:53:05Z` to `22:20:23Z` (`27m18s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`21:54:56Z`; the focal ran to `22:20:10Z`, completed `8,483` jobs and exited
zero. The audit ended at `22:20:19Z` and also exited zero. All four audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9121003880`, named
`flat-generated-qprime-terminal-owner-e781ba4a25bea54229a3679bc1af50536a42a2e2`,
has GitHub digest
`8fba273825ca427adf147e764a64cc42965995d4cc02c7994fdedca6bbc4c275`.
The downloaded deterministic archive has SHA-256
`a9d0760868a56164de18fa059b07da2189167cdba597be49dbbc7e49cfa01f73`,
and all 13 internal manifest entries matched.

The source proves the exact action of the canonical flat generated `Q'` on a
fine coordinate probe: its recursively generated terminal owner receives the
literal coefficient `(M^{-d})^depth`. The reverse coefficient-one synthesis
reads exactly that owner. These two facts derive explicit kernels for both
the source-weighted mass, with coefficient `(M^{-d})^depth`, and Lean's
counting-adjoint mass, with coefficient `(M^{-d})^(2*depth)`, inside one
terminal-owner fibre and zero outside it.

This seals terminal-owner dictionary infrastructure only. It does not
identify the terminal coordinate type with one full coarse block, identify
CMP99 strata, match the generated precision, construct an inverse or produce
a regional Green bound. Regional transport and uniform physical `B0` remain
open. Window 15 remains compatible but unattained. No terminal field is
discharged: counters remain exactly `20/41`, `TermSource = 0`. The successful
Colab v3 diagnostic and the failed v4 syntax diagnostic remain preserved; the
warning-free Colab v5 PASS did not seal. Only the cold run above retires the
two PRE-VALIDATION marks.

### Step 7.5cmn direct generated-owner mass kernels (SEALED; physical precision and stratum dictionaries open)

Exact source checkpoint `1466264a8a568b9d3da1749a8d4e686502f95ea4`
passed cold GitHub Actions run
[`31549159604`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31549159604)
with workflow checkpoint `d9d93cf8b1c1e9188a2ca9da303812932ed0daaf`.
The job ran from `00:08:55Z` to `00:34:33Z` (`25m38s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`00:10:41Z`; the focal ran to `00:34:24Z`, completed `8,484` jobs and exited
zero. The audit ended at `00:34:31Z` and also exited zero. All three audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9124113566`, named
`flat-generated-qprime-direct-owner-kernel-1466264a8a568b9d3da1749a8d4e686502f95ea4`,
has GitHub digest
`cb701f2f6c25039caf9419734a64a7eace8cba86ac1e373529d7e542521b32ec`.
The downloaded deterministic archive has SHA-256
`b26710fd7aeb3afb6e93191c52137f60091d43010be3bc1bd29d6be2c457ea93`,
and all 13 internal manifest entries matched.

The source proves that equality in the dependent terminal-owner type of the
canonical iterated lift is exactly equality of the literal coordinatewise
order-`M^depth` owners. It then rewrites both explicit flat generated mass
kernels to that direct owner test, retaining the exact coefficients
`(M^{-d})^depth` and `(M^{-d})^(2*depth)`. It deliberately does not assert
that an arbitrary active-region fibre has full block cardinality.

This is a dictionary seal only. Physical flat-operator specialization, CMP99
stratum identification, generated-precision matching, inversion, regional
transport and uniform physical `B0` remain open. Window 15 remains compatible
but unattained. No terminal field is discharged: counters remain exactly
`20/41`, `TermSource = 0`. Failed Colab v1 and diagnostic Colab v2 PASS remain
preserved and did not seal; only the cold run above retires the two
PRE-VALIDATION marks.

### Step 7.5cmo generated physical precision at the flat background (SEALED; stratum and inverse dictionaries open)

Exact source checkpoint `5c0eb928fd24f9c9b7598530c3beeccb0921c1cb`
passed cold GitHub Actions run
[`31567100405`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31567100405)
with workflow checkpoint `d71a43397163f2f0aacc5dea478c3f6de3c789f2`.
The job ran from `05:36:24Z` to `06:02:39Z` (`26m15s`). Restore and save of
`.lake/build` were both skipped. Dependency materialization ended at
`05:38:12Z`; the focal ran to `06:02:23Z`, completed `8,485` jobs and exited
zero. The audit ended at `06:02:36Z` and also exited zero. All five audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`; the axiom
blacklist and explicit two-module text and warning gates were empty.

Artifact `9130388288`, named
`generated-flat-physical-precision-kernel-5c0eb928fd24f9c9b7598530c3beeccb0921c1cb`,
has GitHub digest
`10c9ef3ade9f4d269def749a7ff7dfcf515f7e818d46855f8b4ee4856540e166`.
The downloaded deterministic archive has SHA-256
`f8117d060f45918cedf79858cef0448d46f3d566cc7e429629ec17fa0387cb7c`,
and all 13 internal manifest entries matched.

The source specializes the literal generated physical precision internally to
the flat background and the zero-radius source budget. It proves that terminal
codomain transport preserves `Q'^* Q'`, identifies the transported physical
`Q'` with the sealed explicit flat recursion, and exposes the coordinate-probe
kernel as the literal covariant Laplacian plus the separate generated physical
mass. The mass term retains the exact direct-owner test and coefficient
`(M^{-d})^(2*(depth+1))`; neither an operator nor a kernel equality is supplied
by the caller.

This is the flat real physical-operator dictionary only. It does not identify
CMP99 strata, match the recursive generated precision to the separately
constructed one-block full-complex precision, construct its inverse, transport
a regional Green bound or produce uniform physical `B0`. The existing
one-block inverse therefore cannot be reused without explicit carrier,
Laplacian-scale, counting/source-weighted-adjoint, parameter and
complexification dictionaries. Window 15 remains compatible but unattained.
No terminal field is discharged: counters remain exactly `20/41`,
`TermSource = 0`. Colab v1--v7 remain preserved diagnostics; warning-free v8
passed only diagnostically and did not seal. Only the cold run above retires
the two PRE-VALIDATION marks.

### Step 7.5cmp generated terminal owner collapse (SEALED; full-precision dictionary open)

Exact source checkpoint `69fcd7bd26432b55f72e4c41723dca7014cb1106`
passed cold GitHub Actions run
[`31574048398`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31574048398)
with workflow checkpoint `0a4cee527e7074a6be114c25dbe6a31b10a99c68`.
The job ran for `27m02s`; restore and save of `.lake/build` were both skipped.
The focal completed `8,485` jobs and the focal/audit stages exited `0/0`.
All five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist, explicit
two-module text gate and new-module warning gate were empty.

Artifact `9133165960`, named
`generated-terminal-block-collapse-69fcd7bd26432b55f72e4c41723dca7014cb1106`,
has GitHub digest
`007960d1fe47626cc1d2430772edfbc7c4a3c4aa22fd7daad750c8c22e5fb04d`.
The downloaded deterministic archive has SHA-256
`0227d7a2f955d336380e9f5e418557e5e5cf84dfe76f3b78682d5a53ebe75bce`,
and all 13 internal manifest entries matched.

The source constructs the explicit finite-box equivalence between the
generated fine side and the literal side `M^depth * N`, identifies the
recursive terminal owner with `blockSite (M^depth) N`, and proves the two
normalization identities
`(M^{-d})^depth = (M^depth)^{-d}` and
`(M^{-d})^(2*depth) = ((M^depth)^{-d})^2`.  The final coordinate-probe
statement rewrites the canonical generated counting mass using this literal
one-block owner.  It does not identify a CMP99 stratum or a full precision.

The next dictionary must keep three normalizations explicit: carrier/owner
at block side `M^depth`, the generated counting coefficient (a square of the
one-block source weight) versus the full-complex weighted-adjoint coefficient,
and the Laplacian scale at physical spacing.  Precision equality,
complexification, inverse uniqueness, regional transport and uniform physical
`B0` remain open.  This is dictionary infrastructure, not a terminal-field
producer: counters remain exactly `20/41`, `TermSource = 0`, and window 15
remains compatible but unattained.  Failed diagnostic Colab v1 and diagnostic
Colab v2 PASS remain preserved and did not seal; only the cold run above
retires the two PRE-VALIDATION marks.

### Step 7.5cmq generated precision scalar dictionary (SEALED; operator dictionary open)

Exact source checkpoint `e0692ca78b4d3502226f441c8e61d40c8fa442d1`
passed cold GitHub Actions run
[`31579884743`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31579884743)
with workflow checkpoint `14104829d6ae0ed8dfbd780a0c52e5f68e0798d8`.
The cold job completed in `26m27s`; restore and save of `.lake/build` were
both skipped.  The focal ran from `08:48:29Z` to `09:13:06Z`, completed
`8,486` jobs and exited zero; the audit ended at `09:13:11Z` and also exited
zero.  Of the six audited declarations, the block-side definition uses
exactly `[propext]`; the other five use exactly
`[propext, Classical.choice, Quot.sound]`.  The axiom blacklist, explicit
two-module text gate and new-module warning gate were empty.

Artifact `9135484399`, named
`generated-precision-scalar-dictionary-e0692ca78b4d3502226f441c8e61d40c8fa442d1`,
has GitHub digest
`6ab3d73d09af61ddb96c69c8a528f75a227a52d9ffc28c63a2a8e45173980499`.
The downloaded deterministic archive has SHA-256
`5ceafe08faf2996f1d54132a4aa23c1eb316a5be1c95c49c32be854f7f9397a5`,
and all 13 internal manifest entries matched.

The source fixes the terminal block side `R = M^depth`, the corresponding
physical spacing `R^-1` and its inverse-square factor `R^2`.  It then defines
the full-complex averaging coefficient as generated physical mass times the
single source weight `R^-d`, and proves that multiplying by the weighted-
adjoint kernel's second `R^-d` gives the generated counting coefficient
`generatedMass * (R^-d)^2`, including the literal complex cast.  Thus the
two row conventions and their two distinct weights remain visible.

This is scalar dictionary infrastructure only.  It asserts no carrier,
Laplacian, complexification, precision, inverse or regional Green equality;
those operator-level dictionaries remain open.  The diagnostic Colab PASS
with evidence hash
`841b88dffb6beaef66f83727ad275824587a0125b8a862542c7ecca4c31e11f2`
and archive hash
`4ee6f824f78362c4f4ee86b94895a8999012031a7d7748d11e2656f29d6f1d1b`
did not seal.  Only the cold run above retires these two PRE-VALIDATION marks.
No terminal field is discharged: counters remain exactly `20/41`,
`TermSource = 0`, and window 15 remains compatible but unattained.

### Step 7.5cmr full-complex `Q'^*Q'` coordinate kernel (SEALED; operator dictionary open)

Exact source checkpoint `6220199ad49c39cbae3817bda0707efe37a5d9b7`
passed cold GitHub Actions run
[`31589107253`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31589107253)
with workflow checkpoint `0c9caa76797fa93cdbdfdebdfa34dc78faeb0f6f`.
The cold job completed in `19m25s`; restore and save of `.lake/build` were
both skipped. The focal ran from `10:51:28Z` to `11:08:34Z`, completed
`8,544` jobs and exited zero. The audit ended at `11:08:40Z` and also
exited zero. All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`; the axiom blacklist, explicit
two-module text gate and new-module warning gate were empty.

Artifact `9138911003`, named
`full-complex-qprime-mass-coordinate-kernel-6220199ad49c39cbae3817bda0707efe37a5d9b7`,
has GitHub digest
`d153f7d4615cabd33a08f43a22bfe3905a14d616b1d8b5cc819015d45e881f69`.
The downloaded deterministic archive has SHA-256
`1e556c719ee5120048f39fe66ebb64ae77419e6e4fcee3d3855e651e30050c3d`,
and all 13 internal manifest entries matched.

The source constructs an ordinary full-box complex coordinate delta and
proves that the source-normalized block average contributes exactly one
literal block weight `R^-d` on the unique `blockSite R N` owner. Applying
the coefficient-one weighted adjoint yields the exact coordinate kernel of
the literal full-complex `Q'^*Q'`: the same single `R^-d` coefficient on
precisely the targets with the same owner, and zero elsewhere. No fibre-
cardinality identity supplies or hides a second weight.

This is operator-dictionary infrastructure on the full-complex side only.
It does not identify the generated carrier, Laplacian, scalar mass,
complexification, precision, inverse or regional Green operator. The
diagnostic Colab PASS (evidence SHA-256
`5050ae59631d053fd0d1d7e7d874e158889f97c31e86ae8f2d1578fff006a20f`,
archive SHA-256
`deb7ed4e704eb7dc6d64fe21a2aa3b35ba132926be5a78fb4c9ed968820dbacc`)
remains preserved and did not seal. Only the cold run above retires these
two PRE-VALIDATION marks. No terminal field is discharged: counters remain
exactly `20/41`, `TermSource = 0`, and window 15 remains compatible but
unattained.

### Step 7.5cms generated/full-complex `Q'^*Q'` mass coordinate dictionary (SEALED; carrier and full precision open)

Exact source checkpoint `4f72af55fdcb3755d4cb90b0dbc34189ac2a7af0`
passed cold GitHub Actions run
[`31674704480`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31674704480)
with workflow checkpoint `66bc8d13dda9a7038d1cd87c8ac7bc8e1253849c`.
The cold job ran from `06:40:19Z` to `07:01:54Z`; restore and save of
`.lake/build` were both skipped. The focal ran from `06:42:07Z` to
`07:01:46Z`, completed `8,560` jobs and exited zero. The audit ended at
`07:01:51Z`, exited zero and reports exactly
`[propext, Classical.choice, Quot.sound]`. The two-module text gate, axiom
blacklist and new-module warning gate were empty.

Artifact `9171584812`, named
`generated-qprime-mass-complex-coordinate-dictionary-4f72af55fdcb3755d4cb90b0dbc34189ac2a7af0`,
has GitHub digest
`e1590482e4c9cbaec9a02bfe71e99693f4ae4986dcbe7582ecf1eb332d4013f7`.
The downloaded deterministic archive has SHA-256
`3d3e72262588a3cd9a992c21c55546664cb06fdfaed34b88ca2b7cbeeee66585`,
and all 13 internal manifest entries matched.

On a generated active coordinate delta, after the explicit real-to-complex
Lie-fibre embedding, the source proves equality between the generated
counting `Q'^*Q'` mass coordinate and the literal one-block full-complex
weighted-adjoint mass coordinate. The two normalization factors remain
visible: the generated side carries the squared counting weight, while the
complex scalar coefficient and the complex kernel each carry one source
weight. The result is deliberately pointwise and real-source-specific.

No global carrier identification, Laplacian transport, arbitrary complex
source equality, full precision, inverse or regional Green equality is
asserted. Diagnostic Colab v10 PASS (evidence SHA-256
`021663f2cbda002bd5efa9ad96b64b83283bfd8f7b881c0db46b87ea7ae98bd2`,
archive SHA-256
`fdc5c959ca644d838a1c75f624c546ae82e3c3dd0d61e46c5440bd060701ad1f`)
did not seal; only the cold run above retires these two PRE-VALIDATION marks.
This is dictionary infrastructure, not a terminal producer: counters remain
exactly `20/41`, `TermSource = 0`, and window 15 remains compatible but
unattained.

### Step 7.5cmt generated/full-complex `Q'^*Q'` mass field dictionary (PRE-VALIDATION; diagnostic PASS; cold seal in flight)

The source at checkpoint `dbd6e08888129f19b71a93620a2265930c3e0d55`
defines the full-box complex zero extension of an arbitrary generated real
active field as the finite sum of its transported coordinate deltas.  Its
intended endpoint sums the sealed coordinate dictionary over the active
carrier, only at transported active targets and only after the explicit
real-to-complex fibre embedding.  It asserts no global carrier, Laplacian,
full-precision, inverse or regional Green equality.

Diagnostic Colab v1 targeted predecessor
`46ef9dc63b7c84919d458ec57358e64d669712e2` but stopped before checkout
with literal gate output `RAM_GIB=12.67`,
`ERROR=RuntimeError('HIGH_RAM_REQUIRED')`, `FINAL_STATUS=FAIL` and
`RUNTIME_UNASSIGN_REQUESTED=1`.  No Lean, Lake or oracle ran.  Evidence and
reported archive SHA-256 are
`ae69ff4958321cf68ae076a0bcc04870b668cc480601d8b82dcd4a4a35abafa0` and
`bddb988e9f316fe7b8be99b5aba5a01d19ad76a11f0a78c52e78c87bee06e30b`.
Runner v2 checkpoint `46c6f4d54fde45df1cce679e0b8974e0af1482c5`,
opened from high-memory notebook `e123e26daa81273c2126326bc85dd9da58b3395f`,
then passed on exact source `dbd6e08888129f19b71a93620a2265930c3e0d55`:
CPU `50.99 GiB`, focal/audit exits `0/0`, focal `2012.183 s`, audit
`12.197 s`, and literal line `Build completed successfully (8561 jobs).`.
All three declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`cd8a800edafaa084bdad5834c3954e472e14c37dbae330ad6e9e4a700e25d859` and
`2041c6d6416f821f1788cba3243db3e493865a6f08b05ca097574216d6bf0563`.
The runtime auto-unassigned.

Diagnostic PASS does not seal.  The first cold terminal run,
[`31682526462`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31682526462),
workflow `a0454ddfd012bd4b6984c58e96d9e8c257fd9bcf`, `cold=true`, same source
SHA, had restore/save both skipped and focal/audit exits `0/0`, but correctly
failed its seal on one new-module unused-section-variable warning.  Its focal
ended with literal `Build completed successfully (8561 jobs).`; all three
axiom readouts were the allowed trio.  Artifact `9174898524` has GitHub digest
`024f7f5639e3dc0fd5848e57de8c52bbd1038308c8f7bd5958cfcd5eeec2844b`.

Checkpoint `fcdfb890e3a71dafad83623b9a53159022962714` placed the recommended
`omit [NeZero d] [NeZero Nc] in` after the docstring.  Diagnostic v3 rejected
that placement after `1273.312 s` with literal `:51:19: unexpected token
'omit'; expected 'lemma'`.  Evidence/archive SHA-256 are
`437e92d6b6567b7967ebd35e10f11cd5387484366004907a373751ccbe649e51` and
`b5238638ed124058c8660c398e2aef36aebf9eb972fb817408938542e8fae3e0`.
Checkpoint `806fc25bf8b755d15558fe48c415df57d77f6436` moves the same command
before the docstring, matching existing repository syntax without changing
the theorem statement or proof.  Diagnostic v4 passed on that source: CPU
`50.99 GiB`, focal/audit exits `0/0`, focal `1448.555 s`, audit `9.240 s`,
literal `Build completed successfully (8561 jobs).`, and the allowed trio for
all three declarations.  Evidence/archive SHA-256 are
`e8d02e5b4446f00a158c45a85dd5a0e9881a3faa9bd1a91536ae41a3f472488f`
and `526d236504dfcd357d357bcfcd7033b709d848554782f6541d8f58a22aaa3f46`.
Diagnostic PASS did not seal.  Cold terminal workflow checkpoint
`ae36dd874b7db24c20225356b281d6ecad68683a` then ran exactly once as
[`31690217932`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31690217932),
with `cold=true` and source fixed to
`806fc25bf8b755d15558fe48c415df57d77f6436`.  Restore/save were both
skipped; focal/audit exited `0/0`; the focal ended with literal
`Build completed successfully (8561 jobs).`; all three declarations printed
exactly `[propext, Classical.choice, Quot.sound]`; and the corrected source
emitted no linter warning.  Artifact `9177854419` has GitHub digest
`e2f69e025319cc595d4f2fa4a93ba106958fc05e97fbc5496f62180aefaa0913`;
the deterministic archive SHA-256 is
`ffbe6a500d8e2b47fef2c74ca1d90a820aaa79f6850001dae260edb7301fa69e`,
and its 13-entry internal manifest verifies with zero mismatch.  The cold run
seals both modules, so their PRE-VALIDATION marks are removed.  Counters
remain exactly `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.

With this brick sealed, the next full-precision dictionary is a finite chain,
not a free carrier identification:

1. prove, at every full-box site, that the explicit finite sum of deltas is
   the complexification of `extendZeroZeroCLM`, transported through
   `cmp99GeneratedFineBoxOneBlockEquiv`; the inverse equivalence may be used
   internally in this theorem but is not an input to the field constructor;
2. retain the generated active field and this certified zero extension;
3. rewrite the regional Dirichlet Laplacian with
   `cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression`;
4. prove the named background dictionary
   `cmp99SourceFlatGaugeConfig = cmp99FlatGaugeBackground`; both are literal
   unit fields, but no definitional identification is assumed;
5. specialize the ambient operator with
   `cmp99GeneratedAmbientScaledCovariantLaplacian_one_apply`;
6. prove that `cmp99GeneratedFineBoxOneBlockEquiv` commutes with `shift` and
   `shiftBack`, then complexify the literal stencil with
   `cmp99FlatPeriodicComplexFibreStencil_complexification`;
7. expose `spacing⁻² = (M^(depth+1))²` through the sealed scalar dictionary;
8. consume this field-mass dictionary for the separate `Q'^*Q'` summand;
9. identify the compressed generated action, only on active targets, with
   `cmp99SourceFlatFullComplexPrecisionAction 0 A` on the zero extension.

The terminal `0` is the mass argument of the full-complex action; `A` is the
already named generated averaging coefficient.  The chain does not assert a
global equality between the generated active carrier and the periodic full
box.  Inverse uniqueness, regional Green transport and uniform physical
`B0` remain later obligations even after this action dictionary closes.

Step 1 is now present at PRE-VALIDATION checkpoint
`4e17bd3f073f97227b7268c98500e4de63e96e53`: the explicit transported sum
of complex deltas is compared globally, site by site, with the
complexification of `extendZeroZeroCLM`.  The proof splits on active-site
membership and uses the canonical finite-box equivalence only by injectivity;
it introduces no carrier equality.  Source/audit Git-blob SHA-256 are
`5df8605fbd752112969b0dd88ac8e6b60aa03e5749330faee3257c3f6bb988d2`
and `03f2c214024eeb588fa139ab8ec4b515f0f5b0d8567d00441613b7cae3099343`.
It remains compiler-unverified and does not move `20/41`.

Diagnostic v1 reached the new theorem and failed only because the proof had
not rewritten the finite sum of functions with `Finset.sum_apply` before
using `sum_eq_single`/`sum_eq_zero`.  Evidence/archive SHA-256 are
`5ed984086212480b0ab4657ddc28696de7b5d8e6100131316874d8c3bb090c50`
and `3565d14e9539c8927393faa86a11e2fc23b9c4649939727bd59a0e0ab3e2056c`.
The repair is phase-only; the statement and dictionary boundary are
unchanged.  Corrected source checkpoint
`20e5c723aa9b9f05eb83d2a58f5af59f3790fd1e` has source/audit Git-blob
SHA-256
`a85f14c5b5b0f0714f8a88649555fd8b6b6fe9b83ae385959ba6a7d0438aaabe`
and `03f2c214024eeb588fa139ab8ec4b515f0f5b0d8567d00441613b7cae3099343`.
PRE-VALIDATION remains.

Diagnostic v2 consumed that phase repair and reached both literal delta
branches.  It stopped after `2013.813 s` on two residual implications of the
same form, `x = source → complexifiedValue = 0`: broad simplification had
expanded the equivalence before using the named inequality between the two
transported targets.  Evidence/archive SHA-256 are
`40779ac0bb4a6cb6655824f6c65e30f8970ac4e056def7cc544e769339cad6df`
and
`f8864d1f6e3c933eb923581e2e225117d444fe6938b017faab9b75b7aa34e574`.
The runtime auto-unassigned.  The minimal follow-up unfolds only the delta
and rewrites by `if_neg` before simplification.  Repair checkpoint
`4ab330ca87b22be7a1dbd2258e5cd884e64b6f0e` has source Git-blob SHA-256
`1276d78784d94b983f70cd2e67fd42b3e745ae5f7ce02181417e279635647f13`;
runner v3 is fixed by checkpoint
`d046f2fad51d362906f235bd93ddd98569125b1c`, runner-blob SHA-256
`fe5b55862405d174c266be83ad47c0640af316d4ca4861842e714d9551f254c3`.
It passed diagnostically: focal/audit `0/0`, focal `1388.315 s`, literal
`Build completed successfully (8562 jobs).`, and exactly
`[propext, Classical.choice, Quot.sound]` for the new declaration.
Evidence/archive SHA-256 are
`3649719f639da1d94deac23fdef2e1c7e11d7ed469ebab32c3730210f223624e`
and
`0b441a693ae1ff5b9c4f9927a2c62c47eb93beae51efbab56b9e20dcd28ed058`;
the runtime auto-unassigned.  The diagnostic exposed one new-module linter:
`[NeZero d]` and `[NeZero Nc]` are unused.  The source now omits those two
instances explicitly before the theorem docstring.  Warning-repair checkpoint
`af040627262aef1b5109fba114e2184c24a6665f` has source Git-blob SHA-256
`912f57212559dd615bf5fb076e56a5f789edcb74e454d7cbe50a0b3a062652b5`;
runner v4 checkpoint `d3409b2719de255163911619b35fdb076f88d5ca`
has blob SHA-256
`09cf0fb558a639a1da8ef90ec26d190690b1a569e8c73c32e07ff13fdb6ae771`.
No statement, carrier claim or quantitative datum changes; PRE-VALIDATION
and `20/41` remain.

Diagnostic v4 passed on the warning-repair source: CPU `50.99 GiB`,
focal/audit exits `0/0`, focal `1460.445 s`, audit `8.580 s`, literal
`Build completed successfully (8562 jobs).`, exact allowed trio for the sole
declaration, and no new-module linter warning.  Evidence/archive SHA-256 are
`1e8437364d3b723b1674af179553c73b776547a7f95f5f88bf3d199bc91649b7`
and
`4a5e79209e32a1732d3118a29c0e4148c1594049a76657f5f5e5516d394dd0bc`;
the runtime auto-unassigned.  Diagnostic PASS does not seal.  The workflow
is fixed to exact source `af040627262aef1b5109fba114e2184c24a6665f`
for a single cold terminal run; PRE-VALIDATION and `20/41` remain until its
artifact is audited.

Cold terminal workflow checkpoint
`c2eefe6b05db9df22a9f580c1281227ae362f32b` ran exactly once as
[`31704297052`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31704297052),
with `cold=true` and exact source
`af040627262aef1b5109fba114e2184c24a6665f`.  Restore and save of
`.lake/build` were skipped.  The focal/audit exited `0/0`; the focal ran
`13:21:01Z–13:47:14Z` and ended with literal
`Build completed successfully (8562 jobs).`; the audit ended at `13:47:20Z`
and printed exactly `[propext, Classical.choice, Quot.sound]`.  No new-source
linter warning or axiom/text-gate failure occurred.

Artifact `9183467695` has GitHub digest
`6cf551680e53c1df7b5a1a571b6be6e0ebd0554fe3a77608f09d979d79547ea2`.
The downloaded deterministic archive SHA-256 is
`51165261b0880027214299a25e6b8c49b4cda36f77bc9cebd26ecf88c340213a`;
all 13 internal manifest entries matched.  This seal retires only the source
and audit PRE-VALIDATION marks.  Step 1 of the nine-step action dictionary is
now sealed, but it remains dictionary infrastructure: no carrier equality,
Laplacian, full precision, inverse or Green equality is asserted.  Counters
remain exactly `20/41`, `TermSource = 0`, and window 15 compatible but
unattained.

### Steps 2--3: source-pinned field data and regional compression (PRE-VALIDATION)

Checkpoint `d0de24e630f54dba5d2b852960a0b1fe12653ec7` introduces
`CMP99SourceGeneratedTerminalComplexFieldData`.  Its only stored field is the
literal generated active real field.  The real Dirichlet extension and
transported complex full-box field are computed definitions, so a caller
cannot choose either ambient field or supply a free identification between
them.  The package derives the sealed global extension dictionary and the
existing regional-Laplacian compression theorem for that same active field.

Thus nominal chain steps 2 and 3 are combined without identifying the active
carrier with the periodic full box.  The flat-background dictionary, shift
and stencil transport, spacing normalization, full precision, inverse and
Green comparisons remain later steps.  Source/audit Git-blob SHA-256 are
`77771a74339136b0578bcbf3364f4d941a73a842985f64acf7104a03d75833a6`
and
`0aa8cb34ce0a8566348d1f48eb2d1b44d33dc1952665be8f0bff273f601eb4cd`;
runner checkpoint `3506a92e480526e7b4c17364543a6ec5db2b4612` has blob SHA-256
`c11f5d8d2a9424adb75282232c846b4d44b33c5487e026ea487504b9c285c744`.
Both modules remain PRE-VALIDATION and the live counters remain `20/41`,
`TermSource = 0`, window 15 compatible but unattained.
### Source-pinned terminal field data diagnostic

The first fresh Colab diagnostic at `d0de24e6` compiled the two canonical
extensions and regional-compression endpoint (`8563` jobs; focal/audit
`0/0`; three exact standard axiom blocks), but exposed one unused-instance
warning in the new source.  The source-only checkpoint `48f694ab` narrows
that theorem's instance scope without changing its statement.  It remains
PRE-VALIDATION pending a warning-clean diagnostic and cold seal; therefore
steps 2--3 are not yet sealed and the hard counters do not move.

Runner v2 then stopped before audit on the exact parser error `unexpected
token 'omit'; expected 'lemma'`: the theorem docstring preceded the `omit`
command.  Checkpoint `44d4de58` moves the docstring inside the same `omit`
block without changing the theorem statement or proof.  This is still a
PRE-VALIDATION correction, not a seal.  Steps 2--3 remain open and the hard
counters remain exactly `20/41`, `TermSource = 0`, window 15 compatible but
unattained.

The corrected checkpoint subsequently passed a fresh Colab diagnostic:
literal `Build completed successfully (8563 jobs).`, focal/audit `0/0`, three
exact standard axiom blocks and no new-source warning.  This is diagnostic
evidence only.  A single cold terminal workflow is prepared at `48af41c4`;
the two modules remain PRE-VALIDATION and steps 2--3 remain unsealed until
that cold artifact is audited.

Cold workflow `31719064164` seals exact source `44d4de58`: restore/save of
`.lake/build` skipped, focal/audit `0/0`, literal `8563`-job terminal line,
three exact standard axiom blocks, clean new-source warning gate and local
manifest `13/13`.  Artifact `9189461392` has GitHub digest `fc8162bc...` and
the deterministic archive is `e45eb3d0...`.  Only the two corresponding
PRE-VALIDATION marks are retired.  Steps 2--3 are now sealed dictionary and
compression infrastructure; the flat-background dictionary remains step 4.
No terminal producer is added, so counters remain exactly `20/41`,
`TermSource = 0`, window 15 compatible but unattained.

### Step 4: flat generated-background dictionary (PRE-VALIDATION)

Checkpoint `b29a92d` proves that the source-recursion flat gauge configuration
and the independently named ambient-Laplacian flat background are literally
the same unit `GaugeConfig`.  Neither side is caller data.  This is only the
background dictionary: shift/stencil transport, spacing, full precision,
inverse and Green identifications remain open.  Both source and audit retain
PRE-VALIDATION pending fresh-clone diagnostics and a cold seal; hard counters
remain exactly `20/41`, `TermSource = 0`, window 15 compatible but unattained.

The exact checkpoint then passed a fresh Colab diagnostic with literal
`Build completed successfully (8564 jobs).`, focal/audit `0/0`, one exact
standard axiom block and no new-source warning.  This remains diagnostic
evidence only; a single cold workflow is prepared, and step 4 remains
PRE-VALIDATION until its durable artifact is audited.

Cold workflow `31725899611` seals exact source `b29a92d`: restore/save of
`.lake/build` skipped, focal/audit `0/0`, literal `8564`-job terminal line,
one exact standard axiom block, clean warning gate and manifest `13/13`.
Artifact `9192157649` has GitHub digest `eb613d33...`; deterministic archive
`91c8ba62...`.  Only the two corresponding PRE-VALIDATION marks are retired.
Step 4 is sealed as a background-name dictionary; later shift/stencil,
spacing, precision, inverse and Green steps remain open.  Counters remain
exactly `20/41`, `TermSource = 0`, window 15 compatible but unattained.

### Step 5: flat generated ambient specialization (SEALED)

The new leaf module applies the literal generated ambient covariant Laplacian
to the canonical `realZeroExtension` stored by the step-2 field package.  It
rewrites the source-recursion unit background with the sealed step-4
dictionary and then consumes
`cmp99GeneratedAmbientScaledCovariantLaplacian_one_apply`.  Thus neither the
ambient field nor either background is caller data.

This specializes only the real ambient operator.  The generated-box
equivalence has not yet been proved to commute with `shift` and `shiftBack`,
the complex stencil and spacing-power dictionaries remain open, and no mass,
full precision, inverse or Green equality is asserted.

Cold workflow `31732272415` seals exact source `0d64561a`: restore/save of
`.lake/build` skipped, focal/audit `0/0`, literal `8565`-job terminal line,
one exact standard axiom block, clean warning/text gates and manifest `13/13`.
Artifact `9194618665` has GitHub digest `cf714580...`; deterministic archive
`767506b3...`.  Only the two corresponding PRE-VALIDATION marks are retired.
Step 5 is sealed as a real ambient specialization; shift/stencil transport,
spacing, mass, full precision, inverse and Green steps remain open.  Counters
remain exactly `20/41`, `TermSource = 0`, window 15 compatible but unattained.

### Step 6: generated-box neighbour transport and complex stencil (SEALED)

The generated closed-form fine-box equivalence is a dependent cast along the
already sealed side-length equality.  The new module proves separately that
it commutes propositionally with `shift` and `shiftBack`; it then rewrites all
three sites in every nearest-neighbour summand of the canonical generated
complex zero extension and consumes the sealed coordinatewise
complexification theorem for the flat stencil.

The two dependent box types are not declared definitionally equal.  This step
does not expose `spacing⁻²`, consume the generated mass, identify the full
precision, construct an inverse or transport a Green operator.  Source and
audit were sealed by cold workflow `31748745108` on exact source
`68de67d6`: restore/save of `.lake/build` skipped, focal/audit `0/0`, literal
`8566`-job terminal line, three exact standard axiom blocks, clean warning and
text gates, and manifest `13/13`.  Artifact `9200863771` has GitHub digest
`c4ae6f46...`; deterministic archive `d6cdba0c...`.  Only these two
PRE-VALIDATION marks are retired.  Spacing, full precision, inverse and Green
steps remain open.  Counters remain exactly `20/41`, `TermSource = 0`, window
15 compatible but unattained.

### Step 7a: active flat Laplacian in full-box complex coordinates (SEALED)

Checkpoint `e123abc9` adds one pointwise dictionary on transported active
targets.  The retained real active field fixes both zero extensions; the
source-recursion unit background and canonical generated spacing are internal.
The theorem composes the sealed compression, ambient flat specialization,
neighbour transport and exact spacing-square dictionary to identify only the
Laplacian summand with the corresponding full-box complex stencil term.

The generated `Q'^*Q'` mass remains a separate summand.  No full precision,
inverse or Green equality is asserted.  Counters remain exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

A fresh Colab CPU/high-RAM diagnostic on exact source `e123abc9` passed with
the pinned toolchain and Mathlib revision: focal/audit exits `0/0`, focal
`2149.206 s`, audit `10.219 s`, and literal terminal line
`Build completed successfully (8567 jobs).`.  The single audited declaration
printed exactly `[propext, Classical.choice, Quot.sound]`; the source emitted
no new warning.  Evidence/archive SHA-256 are
`db13c7c410cbad7765b6ae2fd68ef3ed0db94e7a339c527d80dcce2eea63e6ea`
and
`a9ab2e3a40bd5d577da7ebf6647417366c9c498d0728aa9a5e5d6bde7940d92f`.
The runtime auto-unassigned.  This diagnostic did not itself seal.

Cold workflow
[`31754552966`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31754552966)
then validated the same exact source under workflow checkpoint `a03e593c`.
Restore and save of `.lake/build` were both skipped.  Focal/audit exits were
`0/0`; the focal ran from `23:40:28Z` to `00:05:24Z` and ended with literal
`Build completed successfully (8567 jobs).`; the audit ended at `00:05:30Z`
and printed the one exact standard axiom block.  The text, warning and axiom
gates passed.  Artifact `9202783700` has GitHub digest
`590914dcdfa7d0ac543d17cdf233e99fdb21994ec7cae6d571fc1d28e885ee22`;
its deterministic archive SHA-256 is
`bd25fd3180e6437a0b6ee134a1f383aca818787f64398da66e95b755c3c90281`,
and all `13/13` manifest entries matched.  This cold evidence seals step 7a,
so only its two PRE-VALIDATION marks are retired.  Generated mass, full
precision, inverse and Green equalities remain open, with no counter movement.

### Step 7b: generated flat physical precision in full-box coordinates (SEALED)

The next module starts from the literal generated flat physical precision,
not from two caller-supplied operators.  It unfolds that precision only far
enough to expose its two summands, applies the sealed step-7a Laplacian
dictionary and the independently sealed generated counting-mass field
dictionary, and recognizes their sum as the literal full-box complex
precision action.  Canonical spacing, active field, both zero extensions,
generated averaging coefficient and scalar mass zero are fixed internally.

The two budgets remain separate until the endpoint.  No inverse or Green
equality is asserted.  Both new modules retain visible PRE-VALIDATION headers
pending compiler diagnostics.  Counters remain exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

Exact source checkpoint is `7456864edd66404496ae0a9eeaf332d2fc2bcbbb`.
Source/audit Git-blob SHA-256 are
`016cdcc69f9b6dd1a8a2efb9c4a5056c86693c7db8ccdf2f827b8db50173f12f`
and
`29655046dcede299612e6635f6b4ab62bafb00d5786db7277d9ef6c4a2baafc2`.
Runner checkpoint `4cd8be775ac669dc19b51ce07ef824360cdafaf0` has
Git-blob SHA-256
`fba135e20d6f9fd9a02ffda1f35b4b71589a7a6e83d7f33a60c65033ac7778bc`.

The first fresh Colab diagnostic stopped at the focal after `2063.801 s`;
the audit was not run.  Its only unsolved goal was the definitional equality
between the explicit generated terminal complex zero extension and
`D.complexZeroExtension`.  Evidence/archive SHA-256 are
`7f6685908a1d3779877af4460414b61340d8127092a4b9eee2c8478775acf035`
and
`c9bba847f5404eb671a89574f4702603ca14f1feecef86aef981ee57685d9b61`.
The runtime auto-unassigned, and this FAIL is diagnostic evidence only.

Correction checkpoint `2e6c98d20cb63f4d12cafa5db8448c510621ff2e`
adds the existing public definition `complexZeroExtension` to the final
normalization; it changes no statement, constant or hypothesis.  Corrected
source/audit Git-blob SHA-256 are
`4c490ee0165f9db258969807c67cef316eb5021e1568e23e809aeff48b2fbf80`
and
`29655046dcede299612e6635f6b4ab62bafb00d5786db7277d9ef6c4a2baafc2`.
Runner-v2 checkpoint `fa4078c4e1ca7b778df233415d218b6abb76a716`
has Git-blob SHA-256
`7f7425eb5c4d3e9a465168abe40915bde8e922d517829fece22ef58636008630`.
The fresh CPU/high-RAM Colab diagnostic opened at
`2026-08-14T01:06:26.171078+00:00` with `50.99 GiB` RAM and passed on that
exact corrected checkpoint.  Focal/audit exits were `0/0`, with durations
`1505.388 s` and `8.910 s`; the focal ended with literal
`Build completed successfully (8569 jobs).`, and the sole audited declaration
printed exactly `[propext, Classical.choice, Quot.sound]`.  Evidence/archive
SHA-256 are
`12b70f065c674aa40e4b99d7a93509122513bbcbb9a687fbb12281812994af32`
and
`318f9a6bf88e427831dea197f32e506a14705d35fe1b7c80ac73667616f0e5e3`.
The runtime auto-unassigned.  This PASS is diagnostic only: PRE-VALIDATION
remains and no seal or counter movement is claimed.

Cold workflow checkpoint `5d9a709a0886ce37e5d0202a09eb79dcf1fa7230`
is fixed to exact source `2e6c98d20cb63f4d12cafa5db8448c510621ff2e`
for one terminal run with `cold=true`.  Restoration and saving of
`.lake/build` are disabled by that input.  PRE-VALIDATION remains until the
resulting durable artifact is audited.

Cold workflow
[`31761329693`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31761329693)
then sealed that exact source under workflow vehicle
`868252c0a48bea64cd335989dd523630ddc199bc`.  `COLD_MODE=true`; restoration
and saving of `.lake/build` were both skipped.  The focal ran
`01:42:05Z–02:07:40Z`, ended with literal
`Build completed successfully (8569 jobs).`, and the audit exited zero at
`02:07:46Z` with the one exact standard axiom block.  Focal/audit exits were
`0/0`, the warning/text/axiom gates passed, and the durable manifest matched
`13/13` entries.  Artifact `9205203086` has GitHub digest
`8724276c2c417605ef4b4e021d4655c6c1bbf774951416c29864249564454149`;
the deterministic archive SHA-256 is
`0331f9c7b78875996cd3be6994c858dd91341d678a80e3b69b340d8071fff7a1`.

This evidence seals step 7b, so only its source and audit PRE-VALIDATION
marks are retired.  It identifies the literal generated flat physical
precision action, not its inverse or regional Green operator.  No terminal
producer is added: counters remain exactly `20/41`, `TermSource = 0`, and
window 15 compatible but unattained.

### Step 8a: canonical generated flat physical Green (PRE-VALIDATION)

Exact source checkpoint `8712e1a0a3515bd32b021b6aecd990ea1b1715c0`
adds the radius-zero specialization of the generated physical Green.  The
module proves that the accumulated source Poincare error vanishes at every
depth, proves positivity of the canonical generated spacing, and constructs
the Green internally from the literal flat background, zero source budget
and already generated coercivity.  It states both real inverse laws for the
same literal flat precision used by step 7b.

Source/audit Git-blob SHA-256 are
`82946bb75066a9b721685bb115ea7d171bbe8331024e3a44605fa73eed857528`
and
`6bb3b44d59db6b64b29dd235a0900a66be76738dbfb64935eb675bbc2a4d53a6`.
Runner checkpoint `f56ef9c023f331dc505987e6b5e05b41ee8b1454` has
Git-blob SHA-256
`737e11b634ee7d6e3a2a2b097e1590920ad50fe72337bdd0826ce4eae6575b09`.
The exact two-file textual overlay gate passed locally; no Lean or Lake ran
on Windows.

This is a real finite-box inverse construction only.  Complexification,
the full-box complex inverse dictionary, multiplication by `Q'^*`, regional
compression and a uniform physical Green bound remain open.  Both modules
retain visible PRE-VALIDATION headers pending a Colab diagnostic.  No
terminal producer is added: counters remain exactly `20/41`,
`TermSource = 0`, and window 15 compatible but unattained.

The first Colab diagnostic reached exact source checkpoint
`8712e1a0a3515bd32b021b6aecd990ea1b1715c0` and exact Mathlib, then stopped
at the focal before the audit.  Its first error was
`BalabanCMP99SourceGeneratedFlatPhysicalGreen.lean:53:2: failed to prove
strict positivity`; the same focal also exposed one unused `simp` argument
and two stuck `Nc` metavariables in the inverse-law wrappers.  Focal exit was
`1` after `1481.671 s`; evidence/archive SHA-256 are
`425e591607f01857d4061ec668caf6714bb393270c0fcff9e15dab6ed4705cca`
and `25e9ca86dc7ab7c95732c8d1ea8889fb5125aea79325187e5557818850805f85`.
The runtime auto-unassigned.  This is retained as diagnostic FAIL evidence,
not as a compiler verdict on any declaration.

Correction checkpoint `3d5d39a90a968a4bdbb9be49432c6a3378e2147a` proves spacing positivity
from the explicit positive natural power, removes the unused `simp` argument,
and pins `(d, M, N, Nc)` in the two inherited inverse laws.  It changes no
statement, physical constant or hypothesis.  The corrected source/audit
Git-blob SHA-256 are
`b3ba8b8d1fae7c689d4f4a7ed93eb733e6cb639d67d159f97355ba95c09c80c7`
and `6bb3b44d59db6b64b29dd235a0900a66be76738dbfb64935eb675bbc2a4d53a6`.
Runner v2 checkpoint `a8fa21c2a0d19b607470a5a475acbf7ff4fd215f`
has Git-blob SHA-256
`b916f8e0a175bafe047bb9f2cccce129398b87e682e333e96958bafd42b4ff88`.
PRE-VALIDATION and all counters remain unchanged pending a new diagnostic.

The second diagnostic checked out exact corrected source
`3d5d39a90a968a4bdbb9be49432c6a3378e2147a` and eliminated the earlier
positivity and unused-`simp` failures.  It stopped before the audit solely on
the two identity conclusions at lines 85 and 104: the wildcard carrier of
`ContinuousLinearMap.id` left `SUNLieCoord ?m` and hence its additive
instance underdetermined.  Focal exit was `1` after `2007.911 s`;
evidence/archive SHA-256 are
`64c36d521fedb62df09b52877f1fb7bfecece2dab5c6304fd7746f4f132908d1`
and `0237a2e40c433ebcb9207d046029e417e0f3ff53d1e8bd22aeccdf33c88e6525`.
The runtime auto-unassigned.

Correction checkpoint `4f69e5b19bbd9173e6f68c672fb17bc1aa21dbeb`
pins the literal generated active carrier and `SUNLieCoord Nc` in both
identity conclusions, without changing any statement, constant or
hypothesis.  Source/audit Git-blob SHA-256 are
`1c630617b3fc75dfa397dfd971257176942c709fd51ec48a7244da835e170d5e`
and `6bb3b44d59db6b64b29dd235a0900a66be76738dbfb64935eb675bbc2a4d53a6`.
Runner v3 checkpoint `eccdb69bb8f6fb5bdfbb81cbecea18f91644d1c6`
has Git-blob SHA-256
`dd59d7bb6647474f70a780ef5d98751bfd334064f2ff312301dd8387e826e605`.
PRE-VALIDATION and all counters remain unchanged pending another diagnostic.

Diagnostic v3 passed at that exact source and pin.  Focal/audit exits were
`0/0`; the focal took `1984.233 s` and ended with literal
`Build completed successfully (8570 jobs).`, while the audit took
`21.607 s` and printed five permitted
`[propext, Classical.choice, Quot.sound]` blocks.  Evidence/archive SHA-256
are `517b244a88682b70b529050d020de9b0a2e27b394b62b3cb8dc6ad4ef7310b86`
and `895a69000341964c55e4d1a3e304e7a91664c777f15becfda01c876ecd1fea8e`.
The runtime auto-unassigned.  This is diagnostic evidence only; both modules
remain PRE-VALIDATION pending one cold seal, and the live counters remain
exactly `20/41`, `TermSource = 0`, with window 15 compatible but unattained.

Cold workflow
[`31770052264`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31770052264)
sealed exact source `4f69e5b19bbd9173e6f68c672fb17bc1aa21dbeb` under workflow vehicle
`2c775320184cb182bb4853070c44bc515f6a20c5`.  `COLD_MODE=true`; restoration
and saving of `.lake/build` were both skipped.  Focal/audit exits were `0/0`;
the focal ran `04:32:09Z–04:59:35Z` and ended with literal
`Build completed successfully (8570 jobs).`, while the audit ended at
`04:59:47Z` with five permitted axiom blocks.  Artifact `9208318458` has
GitHub digest
`cf45329e426b0f637bf64977f075f36ac27b54b89c9e99f7f52118f95ffb3b49`;
the deterministic archive SHA-256 is
`687a8da3adac22d670c2af7adc6555d422eb0de5233a67892faec70050f1ed82`,
and its manifest matched `13/13` entries.

This seals Step 8a and removes only its two PRE-VALIDATION marks.  It does
not identify the real Green with a complex full-box inverse or prove a Green
decay bound.  Counters remain exactly `20/41`, `TermSource = 0`, with window
15 compatible but unattained.

### Step 8b.1: canonical finite `PiLp` complexification (PRE-VALIDATION)

Source checkpoint `525c82fa93744f814a5389c5718b1bdf05fb22aa`
constructs the complex-linear extension of an arbitrary real finite
counting-Hilbert endomorphism from its actions on real and imaginary parts.
The load-bearing endpoints are exact preservation of composition and the
identity, so the two inverse laws of Step 8a can later be transported rather
than reintroduced as complex hypotheses.

Source/audit Git-blob SHA-256 are
`617a7ca70dfd816a8a64d81c7777eafd145b774436e0cfeaa4b5b29b073aa042`
and `9727fbcbe80eb53b27e552f67c938f3b3feacb7921f3ceb556f3f229b04dd856`.
Diagnostic runner checkpoint is
`14dc50d700565e47bb31345ad28af3f33b2f3fba`; its Git-blob SHA-256 is
`aa93cdd69a1270024ac74fa78b5254cc36d0996427aa5b8d46c86928b1f9d2fa`.
The exact two-file text/import guards pass locally; no Lean or Lake ran on
Windows.  Both modules remain PRE-VALIDATION pending Colab.  This generic
brick does not yet transport to the full physical carrier, identify the
literal complex precision, invoke inverse uniqueness, or produce a terminal
field.  Counters remain exactly `20/41`, `TermSource = 0`, and window 15
compatible but unattained.

**Step 8b.2 norm gate (design fixed, source not yet written).**  The real
generated precision and Green are stored on the counting-Hilbert outer space
`PiLp 2`, whereas the already sealed literal full-box complex precision API
is packaged on the ordinary finite function space.  These must not be treated
as definitionally equal or as carrying the same norm.  The specialization
will first reindex both real operators to the full `FinBox`, transport both
real inverse laws, canonically complexify them, and then conjugate through
`PiLp.continuousLinearEquiv`.  Only after that explicit norm transport may the
Step 7b dictionary identify the resulting precision with the literal complex
action and inverse uniqueness derive `G Q'^*`.  This is a design gate, not a
verified producer, and changes no counter.

Diagnostic v1 on exact source `525c82fa93744f814a5389c5718b1bdf05fb22aa`
reached the focal and failed after `1084.992 s` on five purely algebraic
elaboration goals; its audit did not run.  Evidence/archive SHA-256 are
`90c4d03ee54a47a0bce1c7bc36334f2e5facaf8749650ec82d05ed971742bed9`
and `f4dc743631313fdbdc43f88351f93846df6cf10e5c5e758964a77b1a9b34877f`.
Corrected PRE-VALIDATION source `f70de807e6b6ef39fb5e61a3f1c6a4fb9249e622`
retains the construction and all endpoints, makes the commutative-ring
normalizations explicit, and names the real/imaginary projections of
`ofReal`.  Corrected source/audit Git-blob SHA-256 are
`02692632a374d3e3d8def326f7297c236319f85b833dc35411113d7ffb1aa428`
and `278b67fc6922359fd4037527fba16a101d5b21a088d14d725e177a506c5714c7`;
diagnostic v2 runner checkpoint is
`c74f13706cc00f5cdc705f1133772d8f523cb764`, with Git-blob SHA-256
`9145c9d08189ddebe2c3b912768a5d122ffae7eec6ea4a0d0a31a5890f242d0b`.
The thirteen-declaration audit remains pending Colab.  Counters are unchanged.

Diagnostic v2 on exact source `f70de807e6b6ef39fb5e61a3f1c6a4fb9249e622`
failed its focal after `1518.909 s`; its audit did not run.  The remaining
goals were the literal zero embedding, the second composition occurrence,
and a coordinatewise simplification that exhausted heartbeats.  Evidence and
archive SHA-256 are
`fa2a0792c4f321980043a695a656601c7cef5cc62a6a651966a60dbea527a5ab`
and `e20766093b44015f717f18ba8e5575e5cdcf8b37ee04eefdd49f1ba11efa0888`.
PRE-VALIDATION repair `339d8f56da1d594ba6ef75adb8a975e5d3bb9e12`
closes those goals explicitly without increasing heartbeats or changing any
endpoint.  Its source/audit Git-blob SHA-256 are
`f63b952cf9b7ed17ec588f8b1fcbff1b184e802be194a095bbf0bc40eeed07ef`
and `1f50d5911571e9b27f8b44ac2a10ed809ac2bd0a6fb1d385032caa96a0988927`;
diagnostic v3 runner checkpoint is
`f487238ffbd8b92b0bd7eea7b87a096bf5beb1b7`, with Git-blob SHA-256
`ca4568634ef31b0ac4bb4b114485a8179f3a5d7a8f5850777950e67c5d734464`.
The fourteen-declaration audit remains pending Colab.  Counters are unchanged.

### Step 7b item 5 Gate 5 diagnostic v1 (FAIL; explicit transports repaired)

Diagnostic v1 at source `998605926d036a652595d1fe1ee27975e1ba5597`
reached the new focal after all transport, pin and textual gates.  It failed
only because two local definitions obstructed rewriting: the zero physical
momentum was not exposed as a function equality, and the local `physical`
alias hid the integer-period transport.  The audit did not run.  Evidence and
archive SHA-256 are
`272c9764e2eb8063926833dacb39413f40ce284b409ed6f4d38f93e0c6065821`
and
`824da6f2130d23069e0a3b930d428a8b12d3be1dc80b87a17ee10905e33670e0`.

Repair checkpoint `c99e2bbd4d8b3c24462a59f68b4cbbc3b5ddad81`
states both transports explicitly without changing the theorem statements or
the physical route.  Its source Git-blob SHA-256 is
`515dc3865264dfae973d3cad627f14a450cc40a6a2638b1a7e75c00031f13b91`;
the audit blob is unchanged.  Gate 5 remains PRE-VALIDATION and **NOT CHECKED**
pending diagnostic v2.  It still does not identify the generated Green,
attain window 15, discharge a terminal field, or inhabit `TermSource`.
Counters remain exactly `20/41`, `TermSource = 0`.

Diagnostic v2 at exact source
`c99e2bbd4d8b3c24462a59f68b4cbbc3b5ddad81` is green: focal
`EXIT=0` after `1451.528 s` with literal terminal line
`Build completed successfully (8578 jobs).`, and audit `EXIT=0` after
`9.417 s` with five exact permitted axiom trios.  Evidence/archive SHA-256
are `dce238d589e2cb031e7ad64a2360e0b347609bb9962974bca483d2b19a9dd0f5`
and `3a28a8837e754eb6efb4f6e9f85bbc17e7d2f7b2d17f408bc83be4e354134c7e`.
This remains diagnostic only: PRE-VALIDATION and the exact counters stay in
place pending the one cold seal at the same source.

The single cold seal is now complete in run
[`31858189627`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31858189627)
at the same source.  Restore/save of `.lake/build` were both skipped.  The
focal returned `EXIT=0` with literal terminal line
`Build completed successfully (8578 jobs).`; the audit returned `EXIT=0`
with five exact permitted axiom trios.  Artifact `9240084010` has GitHub
digest
`cc72b15dae55683f8e93371abd8514cf8e614ab8fcb2d1c98885e878964c589f`;
the downloaded deterministic archive SHA-256 is
`ca18f029eba5a4769f2b69295fd6ac9e69a3aaae5bec04e3ff85ed25ba85644f`,
with `13/13` internal hashes verified.  Gate-5 PRE-VALIDATION is retired.
This closes direct stabilized-denominator nonvanishing only; the generated
Green identification and window 15 remain open.  Counters stay exactly
`20/41`, `TermSource = 0`.

Cold GitHub Actions run
[`31784588620`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31784588620)
then sealed exact source `9e2b9b7f8e4ef941330587dab8bf848d25b3159d`
from workflow vehicle `0900d009ce580770dad84f3d09db9730de8e211d`.
Project-cache restore/save were both skipped, the focal ended with literal
line `Build completed successfully (8485 jobs).`, and the audit emitted
fourteen permitted axiom trios.  GitHub artifact id `9213595964` has digest
`be24fee79f248be8c67df7117d29b74438afa519c2157709bf1887175a188e5f`;
the deterministic evidence archive has SHA-256
`8959a2b2818056d90f04ad62196d6418c715be489bca341f68f389ae02422592`,
with zero internal manifest mismatches.  The canonical finite `PiLp`
complexification is therefore SEALED and its two PRE-VALIDATION marks are
retired.  The explicit outer-space conjugation, physical precision
identification, inverse uniqueness and literal `G Q'^*` remain open; this
seal moves neither `20/41` nor window 15 and leaves `TermSource = 0`.

### Step 8b.2: explicit outer-norm transport (PRE-VALIDATION)

Source checkpoint `5f13c04ae1b3bdb97fe17d25055f28509b2416ee`
conjugates the sealed canonical complexification through Mathlib's explicit
`PiLp.continuousLinearEquiv`.  It proves exact composition and identity laws
on the ordinary finite function space and a single ordered theorem that
transports either real inverse law.  Source/audit Git-blob SHA-256 are
`a3e6a28db47137db9a9ed6792a1bbe75fa7aae51058c9b216b0c5d5623c034aa`
and `25c248ec03123bc67fe67a79ad58bfbfed6e1feac1da135a3b74728a25b7bb31`.
Diagnostic runner checkpoint
`5759e0d2fd11ab18cdbbfbb34cc6259a4905a7ec` has Git-blob SHA-256
`3adcf357148dd1ffa8ebc794b0d8fee44692985f35981c28f5f51874bd6e8343`.

This is a norm/carrier transport brick only.  It does not identify the
reindexed real precision with the literal physical precision, derive the
literal Green by inverse uniqueness, attain window 15, move `20/41`, or
inhabit a `TermSource`.

The first diagnostic attempt is `INCOMPLETE-RUNTIME-LOSS`: its persisted
transcript reaches the focal command but contains no focal exit, audit,
archive, `FINAL_STATUS`, or unassign sentinel.  The identical-source rerun is
green.  Its focal exited zero after `1469.267 s` with literal terminal line
`Build completed successfully (8486 jobs).`; its audit exited zero after
`12.680 s` with six permitted axiom trios.  Evidence/archive SHA-256 are
`c4ca6bf8d59e3f3d7b4b410c0bb5c0eb02e079be9634bbde1c6d14c6e0a9c06c`
and `14300045fdc62cabaf5962b005e6a3dcb968aa27f78a375a46932cbcf076a72b`.
This is diagnostic only: both modules remain PRE-VALIDATION pending the
single cold seal at exact source `5f13c04ae1b3bdb97fe17d25055f28509b2416ee`.

The post-seal route is finite and ordered.  It must not be collapsed into a
single informal "reindexing" step:

1. add exact composition, identity and ordered inverse-law transport for
   `finitePiLpTypedKernelReindex`;
2. reindex the internally generated flat real precision and Green through
   `cmp99SourceGeneratedPhysicalFullSiteEquiv`, retaining both real inverse
   laws on the full carrier;
3. apply the sealed canonical complexification and this explicit outer-norm
   conjugation to those same two operators;
4. assemble the pointwise Step 7b theorem
   `physicalPrecision_complexification_eq_fullComplexAction` into the exact
   full-box complex precision equality, with no caller-supplied operator
   dictionary; and
5. feed the resulting literal left inverse to
   `cmp99SourceFlatFullComplexPrecisionStabilizedFieldCLM_eq_inverse_comp` to
   derive the literal `G Q'^*` field.

Only item 5 reaches the physical Green endpoint.  A green prefix through any
earlier item remains carrier/norm/dictionary infrastructure and moves neither
the terminal counter nor window 15.

**Factorization gate.**  The full generated carrier has the arithmetic
identity
`M^(depth+1) * (2 * (M * Q)) = M^(depth+2) * (2 * Q)`, but these two
factorizations must not be substituted for one another inside the literal
`Q'` precision.  Step 7b fixes block side `M^(depth+1)` and coarse carrier
`2 * (M * Q)`; replacing them by block side `M^(depth+2)` and carrier `2 * Q`
would change the owner map even though the total `FinBox` cardinality agrees.
The next carrier equivalence must therefore target the Step 7b factorization
explicitly (or add only an outer coordinate cast after the physical operator
has been fixed).  Arithmetic equality of total side lengths is not a physical
precision dictionary.

**Mass-zero nonvanishing gate.**  The inverse-uniqueness endpoint in item 5
still consumes the noncentral fine-symbol and stabilized-central-denominator
nonvanishing hypotheses `hfine` and `hstabilized`.  Step 7b fixes the scalar
mass to zero, whereas the existing common-strip lower-bound API assumes a
strictly positive mass.  Those hypotheses must therefore be constructed for
`mass = 0` and the internally generated positive averaging coefficient (or
remain visibly named inputs); they must not be borrowed from the
positive-mass strip by notation.  This gate is downstream of the exact
complex inverse and does not block items 1--4.

There is a second, independent convention gate inside the same obligation.
The literal solver evaluates the central stabilized denominator at
`cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell`, whose real
coordinates are `-2*pi*(ell mu).val/N'` and therefore range in `(-2*pi,0]`.
The sealed mass-uniform real lower theorem
`cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform` assumes instead
the centered cube `|p_mu| <= pi`.  The latter theorem cannot be applied to
the former momentum by notation.  Item 5 must either construct the exact
coarse-momentum centering together with the induced cycle of the finite alias
fibre, or prove nonvanishing directly on the physical uncentered fibre.  In
either route the generated positivity of the averaging coefficient and the
mass-zero fine-symbol nonvanishing must be produced internally; an arbitrary
`hstabilized` input is not a physical dictionary.

Static route audit (not yet compiler-verified): the stabilized denominator
itself must **not** be declared `2*pi`-periodic.  Its central fine-symbol
factor changes under a physical-period shift.  The faithful finite-carrier
route therefore splits `ell = 0` from `ell != 0`.  At zero, the literal base
momentum is already centered and the mass-uniform central lower bound applies
directly.  Off zero, first construct the signed centered representative of
`-ell mod N'` coordinatewise and its exact integer `2*pi` displacement from
the literal base momentum.  On that centered representative, positivity of
the generated averaging coefficient gives a nonzero stabilized denominator;
nonvanishing of the central fine and unit symbols then identifies a nonzero
reduced/full denominator through
`cmp89Eq249CentralFine_mul_reduced_eq_stabilized`.  Transport only the full
denominator with
`cmp89Eq249ComplexFullAliasDenominator_physicalPeriodShift` and the finite
alias-cycle machinery.  Finally recover the literal reduced and stabilized
factors after separately proving the two real fine symbols nonzero at the
uncentered physical momentum.  This route keeps the removable central pole
and the exceptional zero mode visible; treating the stabilized factor as
periodic would be a false dictionary.

The finite implementation list for item 5 is therefore:

1. prove strict positivity of the literal generated coefficient
   `cmp99SourceGeneratedFullComplexA 4 M (depth + 1) spacing 0` from the
   positive source energy coefficient and the positive one-block averaging
   weight;
2. construct the coordinatewise signed centered representative of
   `-ell mod N'`, prove its `|p_mu| <= pi` bound, and exhibit the exact
   integer `2*pi` displacement to
   `cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell`;
3. prove the missing mass-zero central fine-symbol lemma on the centered cube:
   nonzero momentum implies a strictly positive scaled Laplacian symbol;
4. combine that central lemma with the existing noncentral gap to obtain
   nonvanishing for the complete centered alias fibre when `ell != 0`, then
   transport it coordinatewise by the already sealed alias cycle and integer
   periodicity (`Function.Periodic.int_mul`);
5. prove the stabilized denominator directly at `ell = 0`; off zero, derive
   centered reduced/full nonvanishing by
   `cmp89Eq249CentralFine_mul_reduced_eq_stabilized`, transport only the full
   denominator, and recover the literal stabilized factor after proving the
   two real fine factors nonzero; and
6. feed those internally produced `hfine` and `hstabilized` facts to
   `cmp99SourceFlatFullComplexPrecisionStabilizedFieldCLM_eq_inverse_comp`,
   using the item-3 inverse and item-4 precision equality.  The endpoint must
   expose no free scalar nonvanishing family.

Item 4 and item-5 prerequisites 1--3 are now cold-sealed.  Items 4--6 remain
static design evidence until each declaration receives its own focal and
axiom audit.

Exact item-4 source `f6633ff08c45535bd74ba5fcfae20325877ae000`
was sealed by cold workflow
[`31826053877`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31826053877)
under vehicle `b049fa514ccb44901ab050ce6b74f90f06ded7a4`.
Project-graph restore and save were both skipped.  The focal ended with
literal line `Build completed successfully (8636 jobs).`; the audit emitted
eight permitted `[propext, Classical.choice, Quot.sound]` blocks.  Artifact
`9229863826` has GitHub digest
`7cb20af09e52f38856a4de712715180b219de6f631f259e7c5782665ba4be29e`;
the deterministic archive SHA-256 is
`26f82341cfccad2380f0098cc82df784e8a6e8d07ff7767a7674b125fc9957d3`,
with `13/13` manifest entries matching.  This seals the exact ambient
complex-precision dictionary only.  It does not construct the literal Green,
attain window 15, move `20/41`, or inhabit `TermSource`.

Exact item-5 prerequisite source
`6ffd5b73974ef9ce8207d58ea1d5f78e37196c3f` was sealed by cold workflow
[`31841321042`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31841321042)
under vehicle `c4c93462d164314cec454d92cb55b139253c792f`.
Project-graph restore and save were both skipped.  The three focal terminal
lines were, in queue order,
`Build completed successfully (8571 jobs).`,
`Build completed successfully (8531 jobs).`, and
`Build completed successfully (3294 jobs).`; all six focal/audit exits were
zero.  The audits emitted exactly `4 + 4 + 3` permitted
`[propext, Classical.choice, Quot.sound]` blocks.  Artifact `9235064386` has
GitHub digest
`8a8145b1ce87d26f014cc3a60618dd3989c6ba50efb1950ba664418856522efc`;
the downloaded deterministic archive SHA-256 is
`442ad074d5312dcfe1b749f577e98bd4b80f9aff8bce1f411f1bfbbb60b5a7e8`,
with `17/17` manifest entries matching.  This seals coefficient positivity,
signed centering, and central mass-zero fine nonvanishing only.  Complete
fibre nonvanishing, the stabilized denominator, Green identification, window
15, every terminal field and `TermSource` remain open; counters stay exactly
`20/41`, `TermSource = 0`.

Item-5 gate 4 is now present at PRE-VALIDATION source checkpoint
`12bdcd473d8b9892a0a3f5a825cb78461734472a`.  It proves, subject to compiler
validation, that a nonzero coarse mode gives a nonzero signed centered base
momentum; combines the central mass-zero lemma with the noncentral real gap
over the complete literal alias fibre; and transports that *fibre-wide
property* through coordinatewise integer physical periods using the sealed
alias-cycle permutation.  It never transports the stabilized denominator.
The exact source/audit Git-blob SHA-256 values are
`5d31ec998b7dc5208de221f4161a003cb3ca9e22ac48b74ab2ce83884029cbad`
and
`465f765819ba56465c8854ce9f0ba138643c22464f7365665e0992eafb1c3846`.
Both modules retain PRE-VALIDATION pending a fresh Colab focal and its
five-declaration audit.  This checkpoint changes no terminal counter.

Diagnostic v1 at exact source `12bdcd473d8b9892a0a3f5a825cb78461734472a`
passed every transport, toolchain, pin, cache and textual gate, then stopped
the focal at six elaboration boundaries after `1673.919 s`; its audit did not
run.  The first error was the uncancelled product in the proof that nonzero
coarse mode gives nonzero centered momentum.  Evidence/archive SHA-256 are
`93133b86d917b891c2cfbac125c336a092fb4bf8a8095ceca3e95a30b258f339`
and `a4984aae494b241c2132ff98f76ada6b60119ee21ab9d54977bdf9278a895565`.
Repair checkpoint `9838dcada8c05e1afe1cb451c899fbb91150a44c` changes no
statement: it exposes exactly those six elaboration boundaries.  Its repaired
source Git-blob SHA-256 is
`a2e872afed46de0493ad9883d37a5f21d9c02a61d94915502fd8d0ba4cdfbac0`;
the audit blob remains
`465f765819ba56465c8854ce9f0ba138643c22464f7365665e0992eafb1c3846`.
Gate 4 remains PRE-VALIDATION pending diagnostic v2.  Counters stay exactly
`20/41`, `TermSource = 0`; the stabilized denominator and window 15 remain
open.

Diagnostic v2 at `9838dcada8c05e1afe1cb451c899fbb91150a44c` removed four of
the six v1 errors and stopped after `1098.441 s` at the two remaining
elaboration boundaries: conversion of plain Pi zero to the named zero alias,
and rewriting a dependent subtype projection in place.  Evidence/archive
SHA-256 are
`6ac62dece3241ad6879be22a43a262d881db56f1a890d5bbe2ada3ae0130da1c`
and `b6981ab103f6ccfeaccc249a923caddfecd42b04d57ed6aaf90570a2e635f01a`.
Repair checkpoint `a7131fdb05c32c4956a8cf1bba8f8e7b1d907f13` makes both
identifications explicit and removes the two linter warnings without changing
any statement.  Its source Git-blob SHA-256 is
`a6a3574a73eb99a16de0de2ebde1291103b04f2a8f21759f92899f03c26e547e`.
Gate 4 remains PRE-VALIDATION pending v3 and changes no counter.

Gate 4 is now cold-sealed at exact source
`a7131fdb05c32c4956a8cf1bba8f8e7b1d907f13`.  Fresh Colab diagnostic v3
returned focal/audit exits zero, literal terminal line
`Build completed successfully (8535 jobs).`, and five exact permitted axiom
trios.  The single cold terminal workflow
[`31852173144`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31852173144)
checked out the same source with project-graph restore and save both skipped,
reproduced the same terminal line and five axiom trios, and produced a durable
archive with SHA-256
`b48f45986d2f71989eb000972a38918844293e2d80806a4f5426df4e2a9d561a`;
all `13/13` manifest entries verify.  The source PRE-VALIDATION header is
retired.  This closes item-5 gate 4 only: the literal stabilized denominator,
Green identification, window 15 and every terminal field remain open.
Counters stay exactly `20/41`, `TermSource = 0`.

Static refinement after reading the exact mass-uniform APIs: gate 5 does not
need a new positive-mass or strip estimate at the centered representative.
`cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform` already applies
at `mass = 0`; strict positivity of the internally generated `a` makes its
explicit floor positive.  Likewise, the missing central fine-symbol lemma can
be reduced to
`one_div_three_pi_mul_abs_le_cmp89Eq245ScaledDifferenceNorm` after choosing a
nonzero coordinate.  Thus the new analytic content is limited to central
mass-zero positivity; the remaining work is signed centering, exact
integer-period transport and inverse-uniqueness composition.  This remains
static evidence for items 4--6 until their subsequent compiler checks.

Item-5 gate 5 now has PRE-VALIDATION source checkpoint
`998605926d036a652595d1fe1ee27975e1ba5597`.  Its five declarations implement
the source-faithful case split.  At `ell = 0`, the literal physical momentum is
zero and the mass-uniform real floor applies directly.  At `ell != 0`, the
centered floor plus central fine-symbol nonvanishing first recover the centered
reduced denominator; only the complete multiplied denominator is transported
through integer physical periods; the physical reduced and central factors
then reconstruct the stabilized denominator.  The final generated
specialization produces strict positivity of `a` internally.  Source/audit
Git-blob SHA-256 are
`aceb025835fe52a464f7770745a7227937dc64715128276e658ac63aba3e844a`
and
`9135c10d79ccb18b0719800c565d14d3abe43bbc4c5252488bded9e238cb06bc`.
Both modules remain PRE-VALIDATION and compiler status is **NOT CHECKED**.
Counters stay exactly `20/41`, `TermSource = 0`; Green identification and
window 15 remain open.

Item 1 now has PRE-VALIDATION source checkpoint
`442ebf8f0b32ab480a6dc476f51ba8ced9b73f68` and a three-declaration audit in
`FinitePiLpTypedKernelReindexAlgebra`.  Source/audit Git-blob SHA-256 are
`027c1ef07863968dccc3e2454cad39ed0be71d0a0a26a18c2e0ed1673807b8e7`
and `3a41f55b57054af87f50c4df21fb5f66801a381564e7ba806cf48926d7823313`.
Runner checkpoint `91e4cb58a89ae793ad5e74e96796d8724a6ff39e` has Git-blob
SHA-256
`0e4b7950152e63a5eaecd801f2d3ef29c8f4b56dacb9a7fe9c4f4bd475edae4f`.
It is independent of the outer-transport module and remains unverified until
its own Colab focal and audit complete; it changes no counter.

Its first diagnostic stopped at one explicit inverse-cancellation atom:
`piLpCongrLeft e.symm (piLpCongrLeft e phi) = phi` remained visible under an
arbitrary continuous linear map.  Repair
`41c07595b6929c333904b734b5911fe74718a2bc` names exactly that carrier-level
identity and changes no public theorem or physical dictionary.  The repaired
source/audit Git-blob SHA-256 are
`263404afc01dd21520a4da88551a09a6884eb8e8815a104c26efd9e75c69d7ff`
and `3a41f55b57054af87f50c4df21fb5f66801a381564e7ba806cf48926d7823313`.
It remains PRE-VALIDATION pending diagnostic v2; the failed v1 moves no
counter and proves no part of the physical endpoint.

Diagnostic v2 is green at `41c07595b6929c333904b734b5911fe74718a2bc`:
focal `EXIT=0`, literal terminal line
`Build completed successfully (8173 jobs).`, audit `EXIT=0`, and three exact
permitted axiom trios.  It exposed only an unused-simp-argument warning in
the identity theorem.  Cleanup
`510ee90e913a44c7ea361ef0ec1c99b902d6911e` removes that redundant argument
without changing a public statement; its exact source Git-blob SHA-256 is
`228d928504d3935b881c1798b844578117aad430f02150e085e5c54a85c0f33a`.
The module remains PRE-VALIDATION pending warning-free diagnostic v3 and its
cold seal.  This still changes no terminal counter.

Warning-free diagnostic v3 on exact source
`510ee90e913a44c7ea361ef0ec1c99b902d6911e` is green: focal `EXIT=0` with
literal terminal line `Build completed successfully (8173 jobs).`, audit
`EXIT=0`, three permitted axiom trios, and no warning from the new source.
It remains diagnostic only pending the one cold seal; item 2 and every
physical endpoint remain open.

The outer-norm transport is now cold-sealed by run `31790383378` at exact
source `5f13c04ae1b3bdb97fe17d25055f28509b2416ee`: cache restore/save skipped,
literal terminal line `Build completed successfully (8486 jobs).`, six exact
permitted axiom trios, and a fully verified evidence archive.  Its two
PRE-VALIDATION marks are retired.  This closes only the explicit outer norm
conjugation.

Item 1, the typed-kernel reindex algebra, is cold-sealed independently by run
`31791819258` at exact source
`510ee90e913a44c7ea361ef0ec1c99b902d6911e`: cache restore/save skipped,
literal terminal line `Build completed successfully (8173 jobs).`, three
exact permitted axiom trios, no source warning, and zero evidence-hash
mismatches.  Its two PRE-VALIDATION marks are retired.  Item 2 may now be
built on a sealed parent; the physical precision and Green remain open and
the counters remain unchanged.

Item 2 is cold-sealed at source checkpoint
`9f05ccceaee703297f276edb0068cc3d18c43baf` in
`BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreen`.  The source fixes the
canonical flat precision internally, transports the internally generated
Green through `cmp99SourceGeneratedPhysicalFullSiteEquiv`, and retains both
real inverse laws using the sealed reindex algebra.  Its source/audit
Git-blob SHA-256 are
`ab1b252314e8b072e3087d5bf2727e8dfd923c7e9043a119d22537bb8c9aa9fc`
and `96025fd7c8d82f6a5133d22e3d8a58b85f25c5a6a330ba1680dd0f7e4a30b192`.
Its diagnostic Colab focal and audit now pass at that exact source: literal
terminal line `Build completed successfully (8622 jobs).`, focal/audit exits
zero, and three exact permitted axiom trios.  Evidence/archive SHA-256 are
`d4745f3318714fc9834431b8d59bb5fd1540d0bec051a21745340525293786bb`
and `ae57a5f85e9838a8f7332390586205d90ce857444da711de9235b3327fbd09f5`.
Cold run `31795074593` checked out that exact source with project-graph
restore/save skipped and emitted literal terminal line
`Build completed successfully (8622 jobs).`; its three audited declarations
have the exact permitted axiom trio.  Deterministic evidence archive SHA-256
is `d3cba7fc94531f322aef239c5be9078f41d18b98370c64f4d533ad3717d08b2e`,
with thirteen verified entries and zero mismatches.  The PRE-VALIDATION marks
are retired.  The brick still does not enter the complex or Step-7b
dictionary.

Item 3 has PRE-VALIDATION source checkpoint
`0eae1b434ef037cae73995c530a79186e4041921` in
`BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreenComplexification`.
It applies the sealed canonical outer complexification to item 2's real
precision/Green pair and transports both inverse laws without accepting any
complex inverse data.  Its source/audit Git-blob SHA-256 are
`d1c95125790b2c62c1458737bbfe0912263d37c68c42bd49a0f57eed08b87cb5`
and `10257b119f42801ba5eafe4d783d2123a1dc8342625308993a7dd18939f9b78c`;
runner checkpoint `dff0f1fac0c4619eebdf71ed70c8eb94a6131de3` has blob SHA-256
`eecc4fa6d79f40d383b38fc389738fc6f1bd458dff4f8efd859a4cbebb1cc9b5`.
Diagnostic Colab now passes on that exact source: focal exit zero after
`1574.640 s`, literal terminal line
`Build completed successfully (8625 jobs).`, and audit exit zero after
`18.365 s` with four exact permitted axiom trios.  Evidence/archive SHA-256
are `0c13e1abfc8bdb914d81e883e9d379fe9727f108287c6bc8dbc60d4b08f5d69b`
and `6415dbfd6eec221e2bb0aebe1bd2069517b9075383ed204943b83770230a36d8`.
Cold run `31799867272` checked out that exact source with project-graph
restore/save skipped and emitted literal terminal line
`Build completed successfully (8625 jobs).`; its four audited declarations
have the exact permitted axiom trio.  Deterministic evidence archive SHA-256
is `5e1ed7511e81d1d1674f6f3394bb67c4ef137aaa0e866183ee098b2e3a4a28c7`,
with thirteen verified entries and zero mismatches.  The PRE-VALIDATION marks
are retired.  The literal complex precision equality and Step-7b physical
dictionary remain open, so counters stay exactly `20/41`, `TermSource = 0`,
with window 15 compatible but unattained.

Diagnostic v4 on exact source `9e2b9b7f8e4ef941330587dab8bf848d25b3159d`
is green: focal exit zero after `1563.921 s`, literal terminal line
`Build completed successfully (8485 jobs).`, and audit exit zero after
`17.372 s` with fourteen copies of the permitted axiom trio.  Evidence and
archive SHA-256 are
`c6bace95465e0ad6a8c9028e061fc040d6a394bb3c6cff5cf69e270daf8d0ba9`
and `29c9b19cfbb60dbf932fcf824d0b6d3cd0ea39304177a0920f534899b36abc0f`.
This remains diagnostic only; PRE-VALIDATION marks and counters stay unchanged
pending the single cold seal at the exact source.

Diagnostic v3 on exact source `339d8f56da1d594ba6ef75adb8a975e5d3bb9e12`
failed after `1342.107 s` only because a `ring` tactic followed a `simp` that
had already closed the goal.  Evidence/archive SHA-256 are
`ca403183eedca95a0dcfa236ca9b1c57d2f60a57d446d7d87faaa9ebd344b9de`
and `e16e04bf0ef2f8716c840dc837ad05f945015b27ce6ad3ccdedc6579f11caade`.
PRE-VALIDATION repair `9e2b9b7f8e4ef941330587dab8bf848d25b3159d`
removes only the surplus tactic; source/audit Git-blob SHA-256 are
`054f1de2cd6637cc06a4af1be8850b36a1d0b6fbe4ed792b40cb12a263638f30`
and `1f50d5911571e9b27f8b44ac2a10ed809ac2bd0a6fb1d385032caa96a0988927`.
Diagnostic v4 runner checkpoint is
`dd4d7a63919335ecd929cdf42598d16f5c33389a`, with Git-blob SHA-256
`50073d1331df469e6dd83743b253e693025435331f15b28779f1605204d17e6a`.
The fourteen-declaration audit remains pending Colab.  Counters are unchanged.

### Step 8b.3 Gate 6: generated physical Green endpoint (COLD-SEALED)

Source checkpoint `d0ea9148c746914a60c4a9af6e187ad701f0cb0c`
contains the single post-Gate-5 endpoint brick.  It transports the internally
generated complex ambient Green through the exact Step-7b field equivalence,
derives its left-inverse law from the sealed ambient inverse and physical
precision dictionary, constructs the zero-mass noncentral fine-symbol family
for every coarse mode, and feeds that family together with the cold-sealed
Gate-5 denominator theorem to inverse uniqueness.  The physical
factorization remains block side `M^(depth+1)` and coarse carrier
`2*(M*Q)`; no arithmetic refactorization to `M^(depth+2), 2*Q` occurs.

Source/audit Git-blob SHA-256 are
`735f1912726256a3acfdbc2783fb85b65dc50efc0932839f459ef4bfa8f7864a`
and
`aece1c37a834af9d9afdc7ef58af0d11fc4dfef7bd3bf9934141f3cc5240475c`.
Both files retain PRE-VALIDATION.  Until the focal and four-declaration audit
pass, the Green equality is NOT CHECKED.  Even after validation this brick
will identify the literal `G Q'^*` field only; it will not prove a regional
Green bound, attain window 15, discharge a terminal field, or inhabit
`TermSource`.  Counters remain exactly `20/41`, `TermSource = 0`.

Diagnostic v1 at exact source
`d0ea9148c746914a60c4a9af6e187ad701f0cb0c` stopped at two explicit
`pow_one` normalizations in the zero-coarse/noncentral branch.  The focal
returned `EXIT=1` after `1646.490 s`; the audit did not run.  Evidence/archive
SHA-256 are
`d3fd50464032f4220fa87ef11f445414dbf075eb6f6588c6e814e23ddd17844e`
and
`44cb446bf4902a081b4d4656571e5f1a9e2f22bf7925fb911ae8e8bbfc47f262`.
The wrapper printed its release request, but an instrumentation monkeypatch
prevented the launcher from disconnecting the runtime.  That defect was
measured rather than treated as mathematical evidence; the still-connected
runtime was reused only for the hot diagnostic v2.

Repair checkpoint `10c80c3579de6f84f6686462e52cf23bf22bb761`
normalizes membership from the depth-one alias carrier `M^1` to `M` and
normalizes the same power in the final real-symbol comparison.  It changes no
public statement, physical dictionary, constant, or hypothesis.  Repaired
source Git-blob SHA-256 is
`3120ad19f781f98e143812672ccef8293b0879639e465edb6de30ad0026d5661`;
the audit blob is unchanged.  Compiler status remains NOT CHECKED pending
diagnostic v2; counters and window 15 remain unchanged.

Hot diagnostic v2 at exact source
`10c80c3579de6f84f6686462e52cf23bf22bb761` passed both textual guards, then
stopped after `37.119 s` at the single remaining carrier transport.  The
direct `simpa only [pow_one] using m.property` did not unfold the dependent
alias subtype, so Lean retained membership in
`CMP89Eq246AliasIndex d M 1` rather than the required centered carrier at
`M`.  No Green-conjugation or endpoint declaration failed, and the audit did
not run.  The repaired checkpoint
`3078a38a710dfdb735b5ecdde65d7a014b9c83ef` first pins membership at `M ^ 1`
and then reduces `pow_one`, following the already sealed carrier-dictionary
pattern.  Its source Git-blob SHA-256 is
`4223dca0923eb7b9682a6c16544a5552eb51b0e9195621b8371e75f791413868`;
the audit blob is unchanged.  No statement, constant, hypothesis, inverse,
or physical factorization changes.  Compiler status remains NOT CHECKED
pending diagnostic v3; counters and window 15 remain unchanged.

Diagnostic v3 ran once in a fresh Colab Pro+ CPU/high-RAM runtime at exact
source `3078a38a710dfdb735b5ecdde65d7a014b9c83ef`.  Runner transport,
toolchain digest, Mathlib pin, source hashes, and both textual guards passed.
The focal returned `EXIT=0` after `1549.086 s` with literal terminal line
`Build completed successfully (8645 jobs).`; the audit returned `EXIT=0`
after `16.124 s` and printed four exact
`[propext, Classical.choice, Quot.sound]` blocks.  Evidence/archive SHA-256
are `298216b87f7482efa08217417dfde941c5eac9a9acfc21f6ac2394f1efb883dd`
and `2ebef3fcc1d33449bd0ee9bde92f85669d3fa7dc961c05412a5cff800321e4f2`.
The runtime was explicitly terminated through the Colab session manager and
the tab closed.  This is diagnostic evidence only: PRE-VALIDATION remains
until the single cold workflow checks the same source with project-graph
restore and save both skipped.  Counters and window 15 remain unchanged.

The single terminal cold workflow
[`31863743950`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31863743950)
sealed exact source `3078a38a710dfdb735b5ecdde65d7a014b9c83ef` under workflow
vehicle `e736572a7b6342c14cd87ed1843981de1659a730` (workflow Git-blob
SHA-256 `a0f3581804d3125bf79c0261e0a9f40b0e45dfc8750b63bcffe264f3545c380c`).
Project-graph restore and save were both skipped.  The focal ran
`04:12:32Z--04:47:17Z`, returned `EXIT=0`, and emitted literal terminal line
`Build completed successfully (8645 jobs).`; the audit ran
`04:47:17Z--04:47:31Z`, returned `EXIT=0`, and printed four exact standard
axiom blocks.  Artifact `9241815547` has GitHub digest
`a4eda6e6fe08d0f49508c66c5e698ac512a5d92a84c179186569b6cd8f8076fd`;
the downloaded deterministic archive has SHA-256
`4601cbd8631279a2dc6c2b9beaa4b8c6201f95d4e8d0a4557b1cee5b7dc8b6a5`,
and all `13/13` manifest entries verify with zero mismatches.  This evidence
retires both Gate-6 PRE-VALIDATION headers.

Gate 6 now cold-seals the literal generated Step-7b Green identification with
no free inverse, precision dictionary, `hfine`, or stabilized-denominator
input.  It still does not prove a regional Green bound, attain window 15,
discharge a terminal field, or inhabit `TermSource`.  Counters remain exactly
`20/41`, `TermSource = 0`; window 15 remains compatible and unattained.

### Step 8b.4 Gate 7: one-mode generated Green Fourier fibre (COLD-SEALED)

Source checkpoint `bcc852cee5e709bff91fad7de26fa21cff754e1f` adds the
first exact Fourier specialization downstream of cold-sealed Gate 6.  For a
single coarse Fourier mode it proposes to collapse the full stabilized field
to the internally generated central stabilized particular solution, then
states the selected reciprocal-fibre DFT and the exact off-fibre zero law.

Source/audit Git-blob SHA-256 are
`1ac7f4c87f28c28f653b91a9a7afffa92194d88d1ff5a9d175a3d1842c761aca`
and
`d2ccb839a72db990c1d014d373b85228f290befee643bb8b1cb37c26f10ea25a`.
Both files visibly retain PRE-VALIDATION and are NOT CHECKED by Lean pending
the fresh Colab focal and four-declaration audit.

Even if validated, Gate 7 supplies only the discrete one-mode side of the
Fourier/operator dictionary.  It does not identify a continuous Brillouin
integral, produce a regional Green estimate or uniform `B0`, attain window 15,
discharge a terminal field, or inhabit `TermSource`.  Counters remain exactly
`20/41`, `TermSource = 0`; window 15 remains compatible and unattained.

Diagnostic v1 stopped before checkout and before Lean.  The outer notebook
verified runner transport, then the child runner failed literally with
`NameError: name '__file__' is not defined` because the inherited launcher
executed it from memory.  The runtime was disconnected and deleted without
reexecution.  This is `BLOCKED-INSTRUMENTATION`, not mathematical evidence;
all Gate-7 declarations remain NOT CHECKED.  Runner v2 removes the ambient
`__file__` dependency and downloads the pinned base runner by raw SHA plus
SHA-256 before importing it.  Mathematical source and both source-blob hashes
are unchanged.

Diagnostic v2 reached Lean at exact source
`bcc852cee5e709bff91fad7de26fa21cff754e1f`.  Toolchain, pin, checkout,
source-hash gates, and both textual guards passed.  The focal stopped with
`EXIT=1` after `1479.761 s`; the audit did not run.  Lean reported two proof
normalization failures: line 60 attempted to rewrite a zero in the wrong
scalar/vector type, and line 96 attempted to rewrite a CLM application still
hidden under the `congrArg` lambda.  Evidence/archive SHA-256 are
`e67a04e70ad2708f2f46553201fdc451e5c1fce1c6e536255adbe6c8023f4872`
and
`fe1c8f134c02d6dfb8dcacdb7552da9fbcc9e1d8c91e6fd944be7dc0c5a043b2`.
The runtime was disconnected and deleted without reexecution and the browser
tab was closed.

PRE-VALIDATION repair checkpoint
`65545ad3084c38831ed3f8bc02124c7d49de3d89` removes the mistyped explicit
zero rewrite and normalizes the CLM application with `simpa only` after beta
reduction.  The public statements, constants, hypotheses, and audit are
unchanged.  Repaired source Git-blob SHA-256 is
`7c24e402dbc4f9d5761bb90a4869fdc73b846742003c857e3902acea931e8166`;
the audit blob remains
`d2ccb839a72db990c1d014d373b85228f290befee643bb8b1cb37c26f10ea25a`.
Compiler status remains NOT CHECKED pending diagnostic v3.  Counters and
window 15 remain unchanged.

Diagnostic v3 ran once in a fresh Colab Pro+ CPU/high-RAM runtime under the
visible account `lluiseriksson@gmail.com`, checking out exact source
`65545ad3084c38831ed3f8bc02124c7d49de3d89`.  Runner transport, official
toolchain digest, Mathlib pin, both source hashes, and both textual guards
passed.  The focal returned `EXIT=0` after `2355.241 s` with literal terminal
line `Build completed successfully (8646 jobs).`; the audit returned
`EXIT=0` after `22.802 s` and printed four exact
`[propext, Classical.choice, Quot.sound]` blocks.  Neither `sorryAx` nor
`ofReduceBool` appeared.  Evidence/archive SHA-256 are
`99dd1e55fdec3cc836fa9de9cd5e9608bb1dd1fe33a6fa72e818e010266ec71b`
and
`bd4bd5dd596b359417629cafd9818903083049ba9019921818df7de9800cac37`.
The runtime was explicitly disconnected and deleted and the sole browser tab
closed.

This is diagnostic evidence only.  Both PRE-VALIDATION headers remain until
the one cold workflow seals the same source with project-graph restore and
save skipped.  Gate 7 remains the discrete one-mode Fourier fibre only;
counters remain exactly `20/41`, `TermSource = 0`, and window 15 remains
compatible and unattained.

The single terminal cold workflow
[`31869674637`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31869674637)
sealed exact source `65545ad3084c38831ed3f8bc02124c7d49de3d89`
under workflow vehicle `c528d0d8f3feda072fcc7b18efc3fa506a30e7c6`.
`COLD_MODE=true`; project-graph restore and save were both skipped.  The focal
ran `2026-08-15T06:33:45Z--07:06:33Z`, returned `EXIT=0`, and emitted literal
terminal line `Build completed successfully (8646 jobs).`; the audit ran
`07:06:33Z--07:06:46Z`, returned `EXIT=0`, and printed four exact
`[propext, Classical.choice, Quot.sound]` blocks.  The new source emitted zero
warnings, and neither `sorryAx` nor `ofReduceBool` appeared.

Artifact `9243434656` has GitHub digest
`1e9053d3d0f84994a85ece64a2340ef5ea503253df34339514094f510f437a8e`.
Its downloaded deterministic archive has SHA-256
`2a79ef827d5c6f35c6655dcc7029a9cbcea72b5ad579c81846c83805582f7fc4`;
all `13/13` internal manifest entries verify with zero mismatches.  This cold
evidence retires exactly the two Gate-7 PRE-VALIDATION headers.

Gate 7 remains a discrete one-mode statement.  The finite post-Gate-7 route
is therefore recorded explicitly rather than identifying a finite DFT with a
continuous integral:

1. reuse and compose the already cold-sealed signed-alias and weighted-adjoint
   orientation dictionaries between the transposed physical row at negative
   sampled momentum and the CMP89 endpoint column factors, including the
   centered half-open alias wrap;
2. identify the one-mode finite synthesis pointwise with the sampled CMP89
   stabilized endpoint integrand, without an integral claim;
3. prove finite-grid Fourier aliasing/periodization from absolutely summable
   continuous coefficients and the already sealed finite-character
   orthogonality;
4. specialize the sealed exponential coefficient estimate to the periodic
   owner metric, with the fine-period/owner-unit conversion explicit and no
   volume factor;
5. reinstantiate or generalize the diagonal carrier `K = L = M` to the
   source-separated scales `(L, K)`, where `L` controls the generated tower
   and independently large `K` controls regional contraction;
6. only then perform regional compression and construct the physical `B0`
   and window-15 contraction.

The scale-separation item is load-bearing: the current Gate-6/7 carrier hardcodes
block side `M^(depth+1)` and coarse carrier `2*(M*Q)`, so it cannot by itself
realize the source freedom `K >> L` used by the contraction.  No prefix of
this list is a continuous Brillouin-integral identification, a regional Green
bound, window-15 attainment, a terminal-field discharge, or a `TermSource`
inhabitant.  Counters remain exactly `20/41`, `TermSource = 0`; window 15
remains compatible and unattained.

### Step 8b.5 Gate 8: pointwise finite Green synthesis (COLD-SEALED)

The cold-sealed checkpoint adds the exact finite pointwise synthesis
downstream of Gate 7.  It expands the internally constructed particular
solution, cancels its literal inverse-volume normalization, and leaves each
summand as the positive physical Fourier character times the already named
transposed stabilized alias coefficient.  No inverse, coefficient family, or
reconstruction identity is accepted from the caller.

The orientation layer is not reproved here.  The existing cold-sealed
`BalabanCMP99SourceFlatQprimeSignedAliasMomentumDictionary`,
`BalabanCMP99SourceFlatWeightedAdjointFourierOrientation`, and
`BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution`
modules already supply the centered half-open alias involution, exact
row/column transport, and physical transpose solution that the next bridge
must compose.

Source/audit Git-blob SHA-256 at the validated source checkpoint are
`70a40b91e2387d3823a6cdf3bd739afd9bb4361fad2dd1c57298bb71c121548f`
and
`bf1d64de62d3a5165b6168ef5a09a87c3d86e01cd54b7a7ae11d22956f774d36`.
Both declarations are cold compiler-verified.  This brick is only a finite
periodic synthesis normal form.  It does not identify
the sum with a continuous CMP89 Brillouin integral, prove finite-grid
periodization, separate the source scales `(L, K)`, construct a regional
`B0`, attain window 15, discharge a terminal field, or inhabit `TermSource`.
Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains compatible
and unattained.

Terminal run
[`31877061903`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31877061903)
verified workflow vehicle `d180802c52a2473ef120ad7bb0e081df86efb130`
against raw source `0e852bb5973c34eef9cfd17cf2b0a8c0f1987658` with
project-graph restore/save both skipped.  The focal ran
`2026-08-15T09:30:08Z--10:02:47Z`, returned `EXIT=0`, and ended with
`Build completed successfully (8647 jobs).`; the two-declaration audit also
returned `EXIT=0` with exactly `[propext, Classical.choice, Quot.sound]`.
Artifact `9245388629` has GitHub digest
`f7215ad829602240d8d7ea21c05a4197c5493d105ee507be55d00b9a2cbdbf59`;
the deterministic evidence archive SHA-256 is
`0753c76cc4c23c1dda0291d21d967807829514a5cdd3264d6e905c3e36e13989`
and its manifest verifies `13/13` files.  Exactly the two Gate-8
PRE-VALIDATION headers were retired after this evidence.  Counters remain
`20/41`, `TermSource = 0`; window 15 remains compatible and unattained.

The exact source checkpoint `b640a744bbf17aea9cf3d05a60a259ebe6ca26c2`
then passed its single-clone Colab diagnostic.  The focal completed the
literal terminal line `Build completed successfully (8647 jobs).`, returned
`EXIT=0` after `1536.746 s`, and the two-declaration audit returned `EXIT=0`
after `10.654 s`; both declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence and deterministic archive
SHA-256 are
`7d6a405a549edffe2a2dd0b890c89b10b1f957f1bb347bb91ee8bcace0648e6b`
and
`072f1468764062366e61004d89d8766d3cadc6544f4488c740d5eed8b55ceb98`.
The runner emitted `FINAL_STATUS=PASS` and requested runtime unassignment;
the launcher disconnected the runtime.  Colab decorated the completed cell as
failed only because IPython displayed the runner's final `SystemExit: 0`
after the PASS.  That UI decoration is not a failed Lean stage.

The diagnostic also exposed one new-module linter warning: the first theorem
carried the unused section instances `[NeZero d]` and `[NeZero Nc]`.  A
warning-only source checkpoint then omitted exactly those two instances.  At
that point the PRE-VALIDATION headers remained pending one cold terminal
workflow with project-graph restore and save skipped.

That warning-only source checkpoint is
`17dd7f2bfaa52d19c12cb69ef04b49890a0b52a9`; its source/audit Git-blob
SHA-256 are the staged values above.  The workflow vehicle targets that raw
SHA and rejects any new-module warning, any axiom outside the standard trio,
or any project-graph restore/save in cold mode.

Two post-Gate-8 gates are now explicit.  The half-open centered alias carrier
is not closed under literal integer negation; row-to-column reflection must
use the already sealed signed residue equivalence and retain the wrap.  Also,
Gate 8 fixes scalar mass zero while the current complex-floor consumer still
asks for `0 < mass`.  The real-slice floor is already mass-uniform in
`cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform`, so the remaining
massless complex-floor bridge is localized: reuse the same vertical variation
budget and replace only the obsolete positive-mass real-floor input.  Neither
gate changes `20/41`, constructs `B0`, attains window 15, or inhabits
`TermSource`.

The sole cold terminal run
[`31873674715`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31873674715)
then rejected the warning-only checkpoint before Gate 8 itself materialized.
All `8646` prerequisites built, but the new file ended with
`unexpected token 'omit'; expected 'lemma'`: the `omit ... in` command had
been inserted between a declaration docstring and its theorem.  The repair
only moves that line above the docstring, matching the established syntax in
the tree; the theorem statement and proof are byte-for-byte unchanged.  The
failed-run artifact is `9244488437`, GitHub digest
`93b347a3cd788b43ed9cc1db4d2f542b6700bfcd789d3f24b01e46c95cbfd492`.
No audit or successful evidence archive exists for that run.  Both
PRE-VALIDATION headers therefore remained and Gate 8 was still NOT
COLD-SEALED at that checkpoint.
The next diagnostic vehicle is revision
`gate8-generated-green-fourier-synthesis-v2`, pinned to repaired source
`0e852bb5973c34eef9cfd17cf2b0a8c0f1987658` and Git-blob SHA-256
`70a40b91e2387d3823a6cdf3bd739afd9bb4361fad2dd1c57298bb71c121548f`.

That repaired source then passed the fresh single-clone Colab diagnostic on
CPU/high RAM (`50.99 GiB`).  The focal returned `EXIT=0` after `1807.618 s`
with `Build completed successfully (8647 jobs).`; the audit returned
`EXIT=0` after `12.408 s` and both declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`517f9f5b74d6b56bd76bec5793bed1d6319b59cd5ad2dd47222514bb2e1aa088`
and
`50ec39c9d7ae63b9deaed858544b91e804b145d4e4c4ecb58283ecf5036655f2`.
The runner emitted `FINAL_STATUS=PASS`; the runtime was explicitly
disconnected and deleted.  This authorized one terminal cold workflow on the
same raw source SHA.  At that point PRE-VALIDATION remained pending that cold
run, and the counters remained `20/41`, `TermSource = 0`; window 15 remained
compatible and unattained.

### Step 8b.6: mass-uniform central complex floor (COLD-SEALED)

Checkpoint `733ecbb60d43b72e04f9740eb825251b397503b8` adds a three-theorem
bridge that removes only the obsolete `0 < mass` premise from the central
complex-floor chain.  It reuses the sealed vertical-variation theorem, keeps
the explicit `CMP89Eq251UniformMassWindow mass` assumption, and obtains the
real-slice floor from
`cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform`.  Source/audit
Git-blob SHA-256 are
`8b87cc9a40b2d8b951b3c16c6042dab9f040f667ff1d81f02d7b3ea05a65b75b`
and
`18d69877b2d7c5a83d261933f611edc43aaac5878e97dca0dfc0776bb3c85154`.

Both files retain PRE-VALIDATION and are NOT CHECKED by Lean.  The brick does
not prove the mass window is preserved by the source flow, attain the scalar
complex window, identify the finite synthesis with a continuous integral,
construct regional `B0`, attain window 15, discharge a terminal field, or
inhabit `TermSource`.  Counters remain `20/41`, `TermSource = 0`; window 15
remains compatible and unattained.

The exact source checkpoint then passed its fresh single-clone Colab
diagnostic on the visually confirmed `lluiseriksson@gmail.com` Pro+ account,
CPU/high RAM (`50.99 GiB`), no GPU.  Runner vehicle
`4161e2396e8c302ca07984fc9516709da07f6034` and runner Git-blob SHA-256
`4688adbe4a8ade1b4eb54e4b1ba8099b06ab8911133c8bff35b88e7457f701a3`
gated the two source blobs above, the official Lean asset and exact Mathlib
pin.  The focal returned `EXIT=0` after `868.597 s` with literal line
`Build completed successfully (8441 jobs).`; the audit returned `EXIT=0`
after `9.720 s`, and all three declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence and deterministic archive
SHA-256 are
`d463928738815e5c26271cfb54de5dda02023719acdfdac3e31a13ff6509df0a`
and
`972e5c63213dcee9067c73ae5a82485d514adb83333d078dad08f85641ceb686`.
The runner emitted `FINAL_STATUS=PASS`; the launcher returned zero, requested
runtime release, and the runtime/tab were closed.  Connected cell time was
`1035.632 s`.

This diagnostic authorizes one terminal cold workflow on the same raw source
checkpoint.  It is not the cold seal: both PRE-VALIDATION headers remain until
durable evidence passes with `.lake/build` restore and save skipped.

A static dictionary gate also rejects a tempting but source-false shortcut.
`cmp99SourceMassParameter` is the flowing averaging coefficient `a_j`, passed
in the denominator's `a` slot; it is not the physical `mass` argument.
Consequently its positive uniform floor cannot discharge
`CMP89Eq251UniformMassWindow mass`.  The physical mass-flow window remains the
separate source dictionary recorded above.  Using `a_j` here would be
type-correct but physically false.

Cold workflow
[`31880056149`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31880056149)
then sealed exact source `733ecbb60d43b72e04f9740eb825251b397503b8`
under workflow vehicle `975b2a883f9f864fcb1ef88dc83847a8cd59ba7f`.
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran `10:41:15Z–10:58:53Z`, exited zero and ended with literal
`Build completed successfully (8441 jobs).`; the audit ran
`10:58:53Z–10:59:01Z`, exited zero and produced the three exact standard
axiom blocks.  The warning, text and axiom gates passed and the durable
manifest matched `13/13` entries.  Artifact `9245977306` has GitHub digest
`41a6ab0ca9d6a18bf55b34fabbeb6abd3f59a5710b658647b94decd8b6cc2388`;
the deterministic archive SHA-256 is
`c74135fc37c5c95b37c18b6ad909f4916eeaf7ead0fee3b7271fffff222d601c`.

This evidence retires exactly the two step-8b.6 PRE-VALIDATION headers.  It
removes only the obsolete positive-mass premise from the already explicit
complex-floor chain; it does not prove preservation of the physical mass
window, finite-to-continuous periodization, a regional `B0`, window-15
contraction, a terminal field or a `TermSource` inhabitant.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.


A second static gate fixes the orientation of the next alias dictionary.
Negating a centered alias while keeping the coarse momentum `ell` fixed does
not produce the physical opposite momentum: it changes
`z(ell) + 2*pi*m` to `z(ell) - 2*pi*m`, while the missing `-z(ell)` lies in
the distinct coarse fibre `cmp99FinBoxFourierNeg ell`.  Therefore no
fixed-fibre permutation may be advertised as the physical row-to-column
reflection.  The faithful route is a cross-fibre equivalence from the fibre
over `ell` to the fibre over `cmp99FinBoxFourierNeg ell`, followed by an
explicit Euclidean carry law for the quotient coordinate.  A later static
check sharpened this gate: the signed alias dictionaries do **not** generally
intertwine with residue reflection alone.  This is a static no-go and design
replacement, not a compiler seal or terminal-field discharge.

### Step 8b.7: centered alias residue reflection (cold-sealed; carrier algebra only)

Revised source checkpoint `3bf925319be2b09c6d77706be64913e9817eb3b4` adds
the residue-preserving equivalence from the printed half-open centered alias
carrier to `ZMod M`, conjugates residue negation to obtain its actual
reflection, lifts it coordinatewise to the centered vector carrier, and
transports it through the explicit depth-one alias-index bridge.  The fifth
audited theorem states that this bridge intertwines the two reflection
actions.  Source/audit Git-blob SHA-256 are
`50a27bed81d489105ba1df211823e1d999b5ac4b20df45b4a88a72ee694c3b58`
and
`b934a5e4618844cc747e70e40971e9057f5f3b66a7356ba015d3651648007082`.

The module deliberately stops at alias-carrier algebra and complete-sum
reindexing.  It does not claim that reflection remains inside a physical
coarse fibre, identify an endpoint phase, equate a finite synthesis with the
CMP89 integral, construct regional `B0`, attain window 15, discharge a
terminal field or inhabit `TermSource`.

Diagnostic v1 reached the focal in a fresh high-RAM Colab clone and stopped
at its first real error after `1629.209 s`: line `95:6` attempted to rewrite
a definitionally equal alias-reflection term beneath an inverse equivalence.
The focal exited `1`; the audit did not run.  Evidence JSON/archive SHA-256
are `caa77e25c2e795397572d4d9ba524f8213b5e079764ca563702042b0eeafd7ea`
and `665f6ca3674fd115eca0aa52e1f76c3b7efc348bf78087b77cf24cd385918ed2`.
The runtime released immediately.  No compiler claim is inferred from the
successfully built prefix.

The source repair replaces only that fragile rewrite by a three-line `calc`
which applies the residue theorem to the exact inverse-equivalence term.
Diagnostic runner v2 checkpoint
`3968bac63c4bd470f22826da967161d4b7b82d94` has Git-blob SHA-256
`a6c8122d2d1b170eb7ad9222fffa43ccba754e404738dea8395ecf01cf15e239`.
It gates the revised source blob and unchanged audit, then executes only the
focal and five-declaration audit stop-on-first-error in one fresh Colab
clone.  Diagnostic v2 passed: literal terminal line
`Build completed successfully (8531 jobs).`, focal exit `0` in `1317.583 s`,
audit exit `0` in `7.102 s`, and all five declarations used exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence JSON/archive SHA-256 are
`54e36fc397d569ebdb71f50a6d1cd68b070b50545fc48bb900d0a1415e75e6ce`
and `1b1112838a57933cd725521b2086dc7946ab684c3320d5d10c9ab42196aec76a`.
`FINAL_STATUS=PASS`, launcher exit `0`, and runtime release were all literal.

Terminal cold workflow
[`31885511354`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31885511354)
then sealed the same source under workflow vehicle
`3ab1e84875cd6c33ab32ea748e2444f8dcd4e415` (workflow Git-blob SHA-256
`fcbd51289a197682c5af8d7531c787e4461fc153afb6cd64a7d60950498bfd7c`).
`COLD_MODE=true`; restoration and saving of `.lake/build` were both skipped.
The focal ran `12:50:00Z–13:12:46Z`, exited zero and ended with literal
`Build completed successfully (8531 jobs).`; the audit ran
`13:12:46Z–13:12:51Z`, exited zero and produced five exact standard axiom
blocks.  The text, import-prefix, warning and axiom gates passed.

Artifact `9247413976` has GitHub digest
`82603ae773fb5710b1cfa91aee02929494529d4e6bfcf12076db513c70d66868`;
the deterministic archive SHA-256 is
`a4f8f9dff0ceb1a03796ef9490cdfb86665b7df17e25b92a06a819c92b39d706`,
with zero mismatches in the internal manifest.  This evidence retires exactly
the two Step-8b.7 PRE-VALIDATION marks.  It seals carrier algebra only:
counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.

The carry obstruction is already concrete in one dimension.  With `M = 2`,
`N' = 3`, coarse residue `ell = 1` and quotient `q = 0`, the fine coordinate
is `1 mod 6`; periodic negation gives `5 = 2 + 3 * 1`.  Thus the negated
coarse residue is `2`, but the new quotient is `1`, not `-q = 0 mod 2`.
The printed signed alias therefore acquires a unit borrow/carry.  The next
physical brick must expose that affine carry as a function of the coarse
residue; it may not claim simple intertwinement with
`cmp99SourceAliasIndexOneReflection`.

### Step 8b.8: periodic Fourier negation between coarse fibres (cold-sealed; affine quotient carry still open)

Independent source checkpoint `80ab41f2839cf9546e19c5a12a68196e45b5d246` adds
`BalabanCMP99SourceCoarseFibreFourierNeg` and its three-declaration audit.
The source proves that periodic Fourier negation is involutive on the literal
`FinBox`, that `cmp99SourceFlatQprimeCoarseAlias` commutes with it, and hence
constructs the exact equivalence from the fine fibre over `ell` to the fibre
over `cmp99FinBoxFourierNeg ell`.  Source/audit Git-blob SHA-256 are
`df6985a32c48a9b3eb44673b93e9be6be915efb3cc527aa0a7f98921c050f991`
and
`3cabe9895f86e647585b378c77f779f49e87254e7e64b6253ed563ad37beede0`.

Static preflight superseded the original `91169e80` source before any
compiler run.  Its coarse-alias proof had attempted to close an equality in
`ZMod N'` directly from one in `ZMod (M * N')`.  The revised source applies
the canonical ring homomorphism along `N' ∣ M * N'`; it does not identify the
two moduli or add a periodicity premise.

This checkpoint deliberately depends only on already sealed coarse-alias and
Fourier-negation modules; it does not import the Step-8b.7 reflection.  It
stops before the quotient carry.  In particular it does not
claim intertwinement with `cmp99SourceAliasIndexOneReflection`, identify an
endpoint phase, construct regional `B0`, attain window 15, discharge a
terminal field or inhabit `TermSource`.  Both files retain visible
PRE-VALIDATION headers and are NOT CHECKED.  Diagnostic runner v2 checkpoint
`f342e9d2bf5fc1c8f87df6111169f91e40a279b9` has Git-blob SHA-256
`e2a49c74a415a852c033716eb0c5e1988cb4868469fd20a5185ab8c9bb95ea25`;
it gates exactly these two blobs and runs only the focal plus the
three-declaration audit.  Counters remain exactly `20/41`, `TermSource = 0`;
window 15 remains compatible but unattained.

Diagnostic v2 reached the revised focal in one fresh CPU/high-RAM Colab clone
and stopped at its first real error after `1595.697 s`.  The canonical
`ZMod.castHom` had already transported the equality to `ZMod N'`; line `58:2`
failed only because the explicit simplification list did not unfold
pointwise negation `((-f) mu)` to `-(f mu)`.  Focal exit was `1`; the audit
did not run.  Evidence JSON/archive SHA-256 are
`4fa255ed37f2113f0b9928052372f5e383bcc92f27812e5eec65c68d229f66d6`
and `db1d11a29079183b707331dd717cc710d54808b7e5f81e5e05b2ce2bda3d3b3f`.
The runtime released immediately after literal `FINAL_STATUS=FAIL`.

PRE-VALIDATION repair checkpoint
`c1f9b5104ea94162b3ccc4d6aec6774a6f92005f` adds exactly `Pi.neg_apply` to
that simplification list and changes no statement, map or hypothesis.
Revised source/audit Git-blob SHA-256 are
`f39b4a46111a5274d264e29ab0c4506abc120a5cf9158b8038944eee47c464b3`
and `3cabe9895f86e647585b378c77f779f49e87254e7e64b6253ed563ad37beede0`.
Runner v3 checkpoint `396f03bea9434fc57c10bd83de3356bae7f7fd5d`
gates the repaired source and the unchanged three-declaration audit.  The
diagnostic result below does not retire PRE-VALIDATION before the terminal
cold seal.  The quotient carry and all downstream physical claims remain open;
counters stay exactly `20/41`, `TermSource = 0`, and window 15 remains
compatible but unattained.

Diagnostic v3 passed in one fresh CPU/high-RAM Colab clone after a separate
standard-RAM launch was correctly rejected before toolchain installation by
literal `HIGH_RAM_REQUIRED`.  The useful run opened at
`2026-08-15T13:59:47.360340+00:00`, checked out exact source
`c1f9b5104ea94162b3ccc4d6aec6774a6f92005f`, reverified both blob gates,
Lean `4.29.0-rc6`, Mathlib
`07642720480157414db592fa85b626dafb71355b`, and both textual guards.  Its
literal focal terminal line was `Build completed successfully (8492 jobs).`;
the focal exited `0` after `1117.577 s`, the audit exited `0` after `5.486 s`,
and all three declarations used exactly `[propext, Quot.sound]`.  Evidence
JSON/archive SHA-256 are
`1aa521768b451ad1808c3d302a6c556751853f224c37b4226904ed4a0e21c5f9`
and `336eeac50300d7b320aa9029ac9b7709e4ea9e27c62e193a9f296217065a40c9`.
The runtime released after literal `FINAL_STATUS=PASS` and launcher exit `0`.

Terminal cold workflow vehicle
`3c171d05eb544da66e55f6bf2f4ca502e5917f07` (workflow Git-blob SHA-256
`9a460d446087a90061d2e685889894f674d8ccdaf3831fca46da3603bcd6d86a`)
was executed once with `cold=true` as terminal run
[`31889853498`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31889853498).
Restoration and saving of `.lake/build` were both skipped.  The focal ran
`14:27:07Z–14:40:31Z`, exited zero and ended with literal
`Build completed successfully (8492 jobs).`; the audit ran
`14:40:31Z–14:40:35Z`, exited zero and produced three exact
`[propext, Quot.sound]` blocks.  All source, toolchain, Mathlib, text, import,
warning and axiom gates passed.

Artifact `9248425721` has GitHub digest
`12ddc1813ccec9ba2e6eaa3a6c890e37903c870e083c97d939115484411d4d19`.
The downloaded deterministic archive SHA-256 is
`3363557a2d193d8481b788434baf5d66224261d1da670b6699e66c286341c1e6`,
and every internal `SHA256SUMS` entry matched.  This evidence retires exactly
the two Step-8b.8 PRE-VALIDATION headers.  It seals no affine quotient-carry
or physical endpoint claim and moves no counter.

### Step 8b.9: Euclidean quotient carry across the two fibres (SEALED COLD; carrier arithmetic only)

Independent source checkpoint `0559a9c849d9ba29a3dab346ffcbf5602ffec532`
adds `BalabanCMP99SourceCoarseFibreFourierNegQuotientCarry` and its
three-declaration audit.  It keeps natural periodic negation, Euclidean
division and the later signed centered-alias convention as three separate
layers.  Its central natural statement is

`q'.val = if ell.val = 0 then (M - q.val) % M else M - q.val - 1`;

the outer remainder is required for the canonical periodic zero at
`ell = q = 0`.  Only after this equality is fixed does the module state the
residue corollary `q' = -q` or `-q-1` in `ZMod M`.  It neither imports nor
identifies the Step-8b.7 centered-carrier reflection.

Source/audit Git-blob SHA-256 are
`1f6a6451dae64d24d3dc92a13248661f00fd003db07396e0c494cbc230e79937`
and `2202b0a3380b493bff9082653c6547351b6839822237f7f4f013212e431eee8b`.
Text/import-prefix guards pass locally; no Lean or Lake ran on Windows.
Diagnostic runner v1 checkpoint
`4e48a361a327dc7351966a9472623756bb9c7f59` has Git-blob SHA-256
`701ab51b2317b48fe4c155bd1d6bd3321306e854206760d2e788f3b5420ed6c7`.
Both modules retain visible PRE-VALIDATION and are NOT CHECKED until that
runner emits a compiler verdict.  Every signed-alias, phase and physical
claim remains downstream; counters remain `20/41`, `TermSource = 0`, and
window 15 compatible but unattained.

Diagnostic v1 reached the focal in one fresh CPU/high-RAM Colab clone and
stopped after `1901.181 s` with exit `1`; the audit did not run.  The first
real error was the mechanical direction of `Nat.mul_lt_mul_right`.  The same
transcript exposed an over-broad natural-subtraction rewrite and a missing
import for the already sealed fixed-fibre quotient equivalence.  Evidence
JSON/archive SHA-256 are
`961b5a63a52b0111f5908526169e57072b3b61733b475d516b55ceb707ba108c`
and
`33dce0b4d4bbdfec3fe9b7b484c0d48e2c440dddf2cc3b2333434d8039d25134`;
the runtime released after literal `FINAL_STATUS=FAIL`.

PRE-VALIDATION repair checkpoint
`e6f399f890c24e19deef5dbdde3e7f0b9ea7ce87` changes no statement, constant
or hypothesis.  It imports the actual quotient dictionary, takes the `.2`
direction of the multiplication-order equivalence, and uses `congrArg` for
the exact subtraction normal form.  Revised source/audit Git-blob SHA-256 are
`5e46ec8badf11870e4f2f0eb7b760df4225fdfb90595fe149512dbefe4e701b6`
and
`2202b0a3380b493bff9082653c6547351b6839822237f7f4f013212e431eee8b`.
Runner v2 checkpoint `e62872d959cbfd66743a30409f2e9ad65757af7c`
has Git-blob SHA-256
`afba3b3defb2a06cd95b91e50ec4f46ce786973035131e654aae499c9fb58e9f`.
Both source files remain PRE-VALIDATION and NOT CHECKED; the counter and all
downstream physical claims remain unchanged.

Diagnostic v2 reached exact repaired source
`e6f399f890c24e19deef5dbdde3e7f0b9ea7ce87` in one fresh Colab Pro+
CPU/high-RAM clone. Runner transport, official toolchain, exact Mathlib pin,
both source blobs and both textual guards passed. The focal stopped after
`1644.003 s` with exit `1`; the audit did not run. The first real error was
the orientation of the multiplication/division cancellation lemma. The same
transcript exposed two further normalization debts: rewriting the fine
coordinate only on the left side of the quotient equality, and reducing the
cast of `M` to zero in `ZMod M`. Evidence JSON/archive SHA-256 are
`0860e914c845478bf5a0049f466f39081f9a9515cb905ae9a9c2c54e5a91c6fc`
and
`3451118705f2697d5680410f1f80bd0f1f7f5b23183e135c93adadc69b0af2f4`.
The runner emitted literal `FINAL_STATUS=FAIL`; the launcher requested
runtime release and the runtime disconnected without reexecution.

PRE-VALIDATION repair checkpoint
`be86a1ccb81dd8c69599245e12b3d7a52d7dae9c` uses the matching
`Nat.mul_div_left` orientation, an `ac_rfl` permutation for the natural
semiring normal form, a left-side-only rewrite of the Euclidean decomposition,
and the literal `ZMod.natCast_self` reduction. It changes no public
statement, constant or hypothesis. Revised source/audit Git-blob SHA-256 are
`94d28e9fcd8e9c0e0c677cbb96399d3fe4d7afdc1bb53a8362e921e49a18779b`
and
`2202b0a3380b493bff9082653c6547351b6839822237f7f4f013212e431eee8b`.
Runner v3 checkpoint `e21c2d541127b8eab6d9e1b2cbbcbade06fa9043`
has Git-blob SHA-256
`7b76ff5323709ad84665bd92cedf003c9ee07ef148a1d365924e7481704d13c6`.
Both source files remain PRE-VALIDATION and NOT CHECKED pending that single
diagnostic. Counters remain exactly `20/41`, `TermSource = 0`; window 15
remains compatible but unattained.


Diagnostic v3 on exact source
`be86a1ccb81dd8c69599245e12b3d7a52d7dae9c` passed in one fresh Colab
Pro+ CPU/high-RAM clone. The focal printed literal
`Build completed successfully (8507 jobs).` and exited `0` after
`1417.604 s`; the audit exited `0` after `6.862 s`. Its three axiom sets were
one `[propext, Quot.sound]` and two
`[propext, Classical.choice, Quot.sound]`. Evidence JSON/archive SHA-256 are
`1c7d78a67da7bbe34eeb13a6aa0c45ee2b209cb6b18b406c5857016cb61cd981`
and
`e4890663d09f0b91b1ea8c33529b8535e28b2e49dc2183e27cc90b1f995ebe68`.
The runtime released and disconnected without reexecution.

This PASS authorizes exactly one cold terminal workflow for the same source
and blob hashes; it does not itself retire the PRE-VALIDATION headers. No
signed-alias, endpoint-phase or physical claim is sealed, and counters stay
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

The single cold terminal run
[`31896349484`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31896349484)
then checked out exact source
`be86a1ccb81dd8c69599245e12b3d7a52d7dae9c` with `COLD_MODE=true`; project
graph restore/save were both skipped. The focal printed literal
`Build completed successfully (8507 jobs).` and the focal/audit exits were
`0/0`. The three axiom blocks were one `[propext, Quot.sound]` and two
standard `[propext, Classical.choice, Quot.sound]` blocks. Artifact
`9250160027` has GitHub digest
`73812fcb416d694719db94f3343434fb7713b7ffba3b2ca39190be0f0f02c409`;
the downloaded deterministic archive SHA-256 is
`4f200835c9142a5cc2048ed32185be3d4bffdfb4df82e05e734e764a5ce16634`,
with all `14/14` internal hashes matching.

This seal retires exactly the source/audit PRE-VALIDATION headers for Step
8b.9. It establishes no signed-alias affine carry or physical endpoint
identity. Counters remain exactly `20/41`, `TermSource = 0`; window 15
remains compatible but unattained.

### Step 8b.10: signed-alias affine carry (SEALED COLD)

Source checkpoint `e73cd91d00e0f241c0b772cb84888d47b34d2df8`
conjugates the two source-pinned signed fibre dictionaries through the sealed
cross-fibre negation equivalence. Its coordinate theorem combines the sealed
Euclidean quotient residue law with the actual centered-carrier reflection:
the output alias residue is the reflected input residue plus the coarse
zero/nonzero unit carry. The reflection corollary is derived from the sealed
depth-one bridge rather than postulated as a second convention.

Source/audit Git-blob SHA-256 are
`d44a8f64a6ec081ce026bf022332a2008bc27d49894e856294838088631c153b`
and
`a4b45c0e5e963f6487befc1a75cc21d059c5ee78dce8feb272aa91c8f4ab9e0b`.
Diagnostic runner checkpoint
`881bec52abe782b6735aefbacc96b814ec4d6cd9` has Git-blob SHA-256
`d0c840c3a2cf1bbda47442658cd9973e5adf2c447cb4f8e16e498c6d77abab1a`.
The two Lean files remain visibly PRE-VALIDATION and NOT CHECKED. Endpoint
phase, finite-to-continuous periodization, regional `B0`, window 15 and every
terminal-field claim remain open; counters stay exactly `20/41`,
`TermSource = 0`.

Diagnostic v1 then passed once in a fresh Colab Pro+ CPU/high-RAM clone on
the exact source and runner above. The focal exited `0` after `1544.845 s`
with literal `Build completed successfully (8539 jobs).`; the audit exited
`0` after `7.382 s`, and all three declarations used exactly the standard
axiom trio. Evidence JSON/archive SHA-256 are
`432a3143978e43b4097d3a608dfb958f30df4cf5876ec89aebcec647ff855f8b`
and
`93f99967f5a8e09e37e8a3ff02f88d16f9321c0a68788332a9b8a467aaa0d6ba`.
The runtime released and the tab closed without reexecution.

This diagnostic PASS authorizes one cold seal but does not itself retire the
two PRE-VALIDATION headers. The brick remains carrier arithmetic only, with
all endpoint and physical consumers still open; counters remain exactly
`20/41`, `TermSource = 0`.

The single cold terminal run
[`31899370629`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31899370629)
checked out exact source `e73cd91d00e0f241c0b772cb84888d47b34d2df8`
under workflow vehicle `7f8bf448bfc891652425941e0f0f0070d284151e`.
It recorded `COLD_MODE=true`; project-graph restore and save were both
`skipped`. The focal exited `0` with literal
`Build completed successfully (8539 jobs).`; the audit exited `0`, and all
three declarations printed exactly `[propext, Classical.choice, Quot.sound]`.
Artifact `9250930709` has GitHub digest
`142de2a783380cfd9c25b4f2de31cb8be0f498a8c81e3b4337d70b06cee31cfd`.
The downloaded deterministic archive SHA-256 is
`45bd61fa2d559836b649a7972f68f63084b44c8c46cf655f24dd14181ba1cb60`;
all `14/14` internal `SHA256SUMS` entries matched, `FINAL_STATUS=PASS`, and
the focal evidence contains no new-module warning.

This cold evidence retires exactly the source/audit PRE-VALIDATION headers
for Step 8b.10. It seals only the affine signed-alias carrier law. Endpoint
phase, finite-to-continuous periodization, regional `B0`, window 15, every
terminal field and a `TermSource` inhabitant remain open. Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

### Step 8b.11: fine-to-coarse endpoint phase (SEALED COLD)

Initial source checkpoint `aec4077a9d4ae7e8b8cec70719ec09c12de0c66e`
introduces the integer endpoint displacement `M*y-x` and keeps its fine-to-
block conversion visibly equal to `M⁻¹`.  The terminal theorem identifies the
positive fine Fourier mode divided by the coarse mode at `y` with the exact
CMP89 entire phase at the source amplitude momentum.  The sign and the scale
are therefore statements, not conventions.

The first fresh Colab diagnostic on that checkpoint stopped at the focal after
`1695.182` seconds.  It found one redundant tactic at source line 62 and two
explicit finite-sum normalizations at lines 73 and 109; the audit did not run.
This is a compiler FAIL, not an infrastructure failure.  Evidence SHA-256 is
`e1bc4c8429cebeaa453ad1789a5e7d219d6f1e9bc2912179328128cac78e7951`;
archive SHA-256 is
`c5fd00c5c49284c369475ae1d53e8d07f9ed0f61dfcfa0aeec31b435b3896bd3`.
The runner printed `FINAL_STATUS=FAIL`, `LAUNCHER_EXIT=1` and requested runtime
release.

Correction checkpoint `234753950b8b2250c74a157da6cfe85feaab6acd`
removes only the redundant tactic and makes `Finset.mul_sum` and
`Finset.sum_sub_distrib` explicit; no statement, sign, scale or hypothesis
changes.  Corrected source/audit Git-blob SHA-256 are
`ec6c91dcce42d2ed50ccd68b15774ffc3d9934c06d7226213706f4aa46df60ef`
and
`ec32bf2d253e0a543dc9c799b1ccc9f7fab9637ea9c9ed8f79c1f232e5028d90`.
Exact two-file text and import-prefix guards pass locally; no Lean or Lake ran
on Windows. Retry runner checkpoint
`91d905d8f6902212b6b1b1e1fe0856e780c495ce` has Git-blob SHA-256
`50273dc7437afc16bbe6da404eef3cd101560b93aadb37fda6a920f675d6a76e`;
notebook vehicle checkpoint is
`1fe27f510d19d61f03dd09577f0432ae2fe57341`.

The second fresh Colab diagnostic eliminated the first two proof failures and
stopped only at line 112 after `1626.611` focal seconds: the left side had been
distributed into a finite sum while the right side still retained
`Complex.I * ∑`.  Evidence SHA-256 is
`4e0df84f5154fcaa0cfff1793dbb9aa2fd84fbb8774bcdc1fb7968ab09b1fa01`;
archive SHA-256 is
`dab2461b310f3cb807090cc618694598a71d6bfc7e14c553dd013ae5092dcdfb`.
Again `FINAL_STATUS=FAIL`, `LAUNCHER_EXIT=1`; the audit did not run and the
runtime release was requested.

Latest correction checkpoint `f7d0e7e7f4d02f92bf60942bbf218788f6d69f5e`
adds exactly the second `Finset.mul_sum` rewrite.  Latest source/audit Git-blob
SHA-256 are
`e03e6d2d0a662dffa283d2b3f3d50751ed7bcd9c8dd9744b0ce26a0f171eafcf`
and
`ec32bf2d253e0a543dc9c799b1ccc9f7fab9637ea9c9ed8f79c1f232e5028d90`.
Runner checkpoint `5330aa7f43e66b568c343f697b213ed919efe63d` first added a
Mathlib-only reproduction before the expensive focal.  That repro stopped in
`7.563` seconds because it used the same summand on both sides: the first
rewrite made the goal reflexive, leaving the second rewrite without a pattern.
No project target ran.  This is `BLOCKED-INSTRUMENTATION`, not a mathematical
failure. Evidence SHA-256 is
`d2fe149a6c9ef57427bf5510ff81dece56dae5454445c8d9f1f24f370bb39d6a`;
archive SHA-256 is
`026e8c4b324078488dbc8f9305cfebf672e51f4a27675c1761b18718ac39dcb7`.

Corrected runner checkpoint `a2b6fc7a096d40e2be440f5b21c0548bcc4a8c4b`
uses a distinct right summand plus a pointwise equality, matching the real
non-reflexive target.  Its Git-blob SHA-256 is
`3f5d52a418b6be5ec8960c9b79a1eb0ec099ea498e8d16458401751897c83fe6`;
notebook vehicle checkpoint is
`325e83c6bfdd5b0b1406bfa2c209a735a47a411e`.

The next fresh Colab run passed the corrected repro (`7.882` seconds), built the
source with literal terminal line `Build completed successfully (8532 jobs).`
(`1685.950` seconds), and ran the audit with exit zero (`9.532` seconds).  The
displacement declaration printed `does not depend on any axioms`; the other
three printed exactly `[propext, Classical.choice, Quot.sound]`.  The wrapper
then emitted `FINAL_STATUS=FAIL` solely because it expected four nonempty axiom
blocks instead of three.  Evidence SHA-256 is
`e843ce461ec34935a5980834e3eab555bb39928594256c0eb76c1c01e655b877`;
archive SHA-256 is
`06ec3db14f981ccd62e3909870cc3299fe6799422e71194e3d2166bdd68700bd`.
Thus focal and audit are green in a fresh clone, but the checkpoint is not yet
cold-sealed because the sentinel verdict was instrumentation-false.

Runner checkpoint `738663c0295dcb3046c3101697bb96a422674d51`
changes only the expected nonempty axiom-block count from four to three.  Its
Git-blob SHA-256 is
`a3e7522b81f9d8d00f41cf4555c6c71dbe2471321029e3a53b7937499f36b832`;
notebook vehicle checkpoint is
`c34eb060e15da0a0834b58f72f981d2f25090ab1`.  Both Lean modules remain visibly
PRE-VALIDATION pending the cold seal.

Terminal workflow checkpoint `222bb84b` adds
`validate-flat-qprime-endpoint-phase.yml`, pinned to source
`f7d0e7e7f4d02f92bf60942bbf218788f6d69f5e` and the two Git-blob hashes above.
It disables project-graph restore/save under `cold=true`, expects exactly three
nonempty axiom blocks, and packages deterministic evidence.  This is a prepared
vehicle only: no terminal run has yet been claimed, PRE-VALIDATION remains, and
no counter moves before the durable cold artifact is audited.

The attempted dispatch of that new filename was rejected before run creation
with literal GitHub response `HTTP 404: workflow ... not found on the default
branch`.  This is `BLOCKED-DISPATCH`, not a terminal run.  Correction checkpoint
`db689e1c` supersedes the undispatchable filename and installs the same pinned
queue in the already registered `validate-localized-carrier.yml`; no source,
statement or evidence claim changes.

The single cold terminal run
[`31909428858`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31909428858)
then executed the registered workflow at vehicle HEAD
`92e2b41d4ac95c1b59dcafbd10ded590525ebe88` and checked out exact source
`f7d0e7e7f4d02f92bf60942bbf218788f6d69f5e`.  It recorded
`COLD_MODE=true`; project-graph restore and save were both `skipped`.
The focal exited `0` with literal terminal line
`Build completed successfully (8532 jobs).`; the audit exited `0`.  The
displacement declaration was axiom-free and the other three declarations used
exactly `[propext, Classical.choice, Quot.sound]`.  Artifact `9253520855` has
GitHub digest
`869f5ed4e6f04e960bfe3a73c18f1bc7e0f420df4eedcc73e0e9db340e40c03c`.
The downloaded deterministic archive SHA-256 is
`cf61120df96559f15bf777c95a3becfd2bc347c5e33dd2d3b7100f1a3e752642`;
all `14/14` internal hashes matched, `FINAL_STATUS=PASS`, and the focal emitted
no new-module warning.  This evidence retires exactly the two Step-8b.11
PRE-VALIDATION marks.

This brick is the unit/phase dictionary only.  It does not yet combine the
sealed Step-8b.10 affine carrier reindexing with the finite synthesis, identify
a Brillouin integral, produce regional `B0`, attain window 15, discharge a
terminal field or inhabit `TermSource`.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.

### Step 8b.12: signed-alias endpoint phase transport (PRE-VALIDATION; NOT CHECKED)

Source checkpoint `1fc19056f0a1fa0782924196687b84b074785679` adds
`BalabanCMP99SourceFlatQprimeEndpointAliasPhase` and its five-declaration
audit.  Source/audit Git-blob SHA-256 are
`5da43c092180dbfa1e892e243b0384fff6fbcff517d03adc35cbef8ed964e9f4`
and
`41adac323d2ea168de171c9d3d97594979e81f104e1ca0946ef7cb3376745ec3`.
Diagnostic runner checkpoint `9733f9c8d0a64bd76620fec0a5ea63e477260d01`
has Git-blob SHA-256
`ef801516097aa7ecad8aee9d90d5b0b38d641ba65081d7db3670d0263eaf58a6`;
notebook vehicle checkpoint is
`60e3125acabcc77f36a8b61edcb11e393a36dd4a`.  The runner executes a
Mathlib-only reproduction of the period-pairing algebra before the expensive
focal and expects four nonempty axiom blocks plus the pure pairing definition.
The brick makes the integer pairing `<w,u>` literal, proves that every vector
of `2*pi*M` alias periods disappears after exponentiation at the physical
fine displacement `M^-1 u`, and transports the Step-8b.11 endpoint quotient
to the signed CMP89 alias momentum constructed by the sealed fibre dictionary.

The orientation gate remains open and visible: the physical synthesis carries
the transposed solution's row amplitude `u(-q)`, whereas the CMP89 bare Green
numerator carries the column amplitude `u(q)`.  No row/column reflection,
Fourier-negation reindexing, finite-sum identity, Brillouin integral, regional
`B0`, window-15 attainment, terminal-field producer or `TermSource` inhabitant
is claimed here.  Both new files remain visibly PRE-VALIDATION and no Lean or
Lake has run on Windows.  Counters remain exactly `20/41`, `TermSource = 0`;
window 15 remains compatible but unattained.

Diagnostic v1 opened one Colab Pro+ CPU/high-RAM runtime under visible account
`lluiseriksson@gmail.com` at `2026-08-15T22:07:27Z`.  Runner transport,
official toolchain digest, exact checkout, both source-blob gates and both
textual guards passed.  The Mathlib-only repro then stopped after `5.866 s`,
before the project focal, with two missing `noncomputable` markers and two
literal `No goals to be solved` reports after `field_simp` had already closed
the goals.  Evidence/archive SHA-256 are
`84fd22b24e9a22f9be6434c1f1110deeb1dc91732e83ccde7375d61a2f52d8ba`
and
`aa00ff7336dfd7245bfc68f452e2bacf4e8e11dc081ae0b7523a5ecc9862b6e7`.
The launcher emitted `FINAL_STATUS=FAIL`, `LAUNCHER_EXIT=1` and released the
runtime.  This is `BLOCKED-INSTRUMENTATION`, not a mathematical failure; no
project Lean target ran.

Runner-only correction checkpoint
`74a36c692878005201c900f7eac48468eef1536c` marks the two repro definitions
`noncomputable` and removes only the two redundant tactics.  Its Git-blob
SHA-256 is
`c692fdefdf8b9102ece2b5ae706e85e4c883c36967abab6c513bacdc9b04b9d1`;
notebook vehicle checkpoint is
`0c85ca9224b53a43df2c902e3b5c2fb8f4a5a19d`.  The mathematical source SHA,
both source blobs, declarations, statements and audit are unchanged.  Step
8b.12 remains PRE-VALIDATION and NOT CHECKED pending the corrected diagnostic.

Diagnostic v3 then checked out corrected source `afad2379` in a fresh Colab
Pro+ CPU/high-RAM runtime.  The repro exited zero in `8.662 s`; the focal
exited zero in `1693.132 s` with literal line
`Build completed successfully (8542 jobs).`; the audit exited zero in
`10.224 s`.  All five audited declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  The runner's sole failure was an
expected-block count of four rather than the measured five.  Evidence/archive
SHA-256 are
`a3c23dc5c3136e8342b54725c50fa1d3512c8ea5dd7f57d6cced2d45a1163e15`
and
`bd0634850ae06c86ee20728b29fc809521e6270bfb9dbb9b2665e5c3de8d6962`.
This is a false instrumentation verdict after green focal/audit; the runtime
was released and the computation is not repeated.

Runner-only v4 checkpoint `a440801c18e4c9a7889c46944ad3ffa89588e209`
has Git-blob SHA-256
`f44af86edf35437258e9b700456193529d6aa3a0268cb19ea28936eeb93c79b1`
and expects the measured five blocks; notebook checkpoint is `6dbde9ce`.
Terminal workflow checkpoint `03a61455` pins corrected source `afad2379`, both
exact source blobs and the five-block gate, with restore/save disabled in
`cold=true`.  PRE-VALIDATION remains until that single cold artifact is
audited.  No counter moves.

The single cold terminal run
[`31914703879`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31914703879)
used workflow vehicle `6a71f63e07574a46e57268325f4b68070c587603`
and exact source `afad237929739252cf850f55f0c273a71bf5a524`.
`COLD_MODE=true`; project-graph restore/save were both `skipped`.  Focal/audit
exits were `0/0`, with literal line
`Build completed successfully (8542 jobs).`; all five declarations used
exactly `[propext, Classical.choice, Quot.sound]`.  Artifact `9254837559` has
GitHub digest
`66ae26c1b8097d3e055fd9566fbc3a820759c304a7388cb585b9ada6f53f5d0e`;
the downloaded deterministic archive SHA-256 is
`f68c457a18de1120e6b831cf520951a038c8477e70e2d80722afc265d31fa200`.
All `14/14` internal hashes matched, `FINAL_STATUS=PASS`, and the focal had no
new-module warning.  Exactly the two Step-8b.12 PRE-VALIDATION marks are
retired.

Step 8b.12 is cold-sealed but remains a phase dictionary.  Row/column
orientation, the complete finite-sum reindex, Brillouin periodization,
regional `B0`, window 15 and terminal fields remain open.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

Diagnostic v2 passed the Mathlib-only reproduction in `7.331 s` but the fresh
Colab focal failed after `1625.702 s` at the new source: a redundant `ring`
followed a goal-closing `field_simp`, and the abbreviation
`CMP99SourceFlatQprimeFixedCoarseFibre` lacked its direct defining import.
Evidence/archive SHA-256 are
`9608e88bf46d26b9880ff1052ca55dd8e2e653b4a9df78dfa23f877ecc0ca042`
and
`786521b87af26f3f44c5de8ecb6659f3cdb35a08226d3b0c22e5cf3297fafd0c`.
The audit did not run; the runtime was released.  This is a measured focal
elaboration failure, not infrastructure or a counterexample.

Correction checkpoint `afad237929739252cf850f55f0c273a71bf5a524`
changes only those two mechanical points.  Corrected source/audit Git-blob
SHA-256 are
`c83042469334a986d8313e5abb42b7eed67eb57f783554aba7e824b393350da8`
and
`41adac323d2ea168de171c9d3d97594979e81f104e1ca0946ef7cb3376745ec3`.
Runner v3 checkpoint `ce03fc3268b1d3d7ee8b363ed87922c111a822a6`
has Git-blob SHA-256
`d39f863283d97f216fdfa1b6c2a69cdc977e3038bcbe51af0fa1a4d0acb82c29`;
notebook vehicle checkpoint is `c2209bd2`.  Statements, constants, hypotheses
and delimitations are unchanged.  Step 8b.12 remains PRE-VALIDATION and NOT
CHECKED pending v3; counters remain `20/41`, `TermSource = 0`, window 15
compatible but unattained.

### Step 8b.13: row-oriented sampled endpoint normal form (cold-sealed; orientation bridge open)

Source checkpoint `62862316ed330ef0efa8db676fa3b3f97b441c6e`
adds `BalabanCMP99SourceFlatQprimeTransposeEndpointSample` and its
three-declaration audit.  Source/audit Git-blob SHA-256 are
`bb7fb89b9366d99eaed0f98105f64a628c562657bc9b54f94f542a29b4415012`
and
`9bc50c439e007be0024db76ee5a807d67689710a2c7d652aa3f0b06cc2965b2a`.
The brick rewrites one physical transpose-Green Fourier summand, and then its
complete fixed-fibre sum, into a named row-oriented endpoint sample using the
cold-sealed endpoint phase.  It inserts no volume or integral normalization.

The orientation gate stays visible: no row-to-column replacement,
cross-fibre Fourier-negation reindex, termwise zero-alias claim, Green
periodization, Brillouin integral, regional `B0`, window-15 attainment,
terminal-field producer or `TermSource` inhabitant is claimed.

Diagnostic runner checkpoint `22a087e5156f34c582b37798624b1a626297cac2`
has Git-blob SHA-256
`7282f931d1bdc66f73cadd0248596ec28334cb4cde2577d566dd04683b5fab42`;
notebook vehicle checkpoint is `e2159c58`.  Its Mathlib-only repro checks the
two algebraic rewrites before the expensive focal.  Both files remain visibly
PRE-VALIDATION and NOT CHECKED; no Lean or Lake ran on Windows.  Counters stay
`20/41`, `TermSource = 0`; window 15 remains compatible but unattained.

The one-clone Colab Pro+ diagnostic is green at the exact source SHA
`62862316ed330ef0efa8db676fa3b3f97b441c6e`: repro/focal/audit exit
`0/0/0`, literal focal line `Build completed successfully (8657 jobs).`, and
all three audited declarations have exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`90366e317240975eb2ae5cc011404ce90c969b9d34ac55afaff010804f0a81ff`
and
`39403b815f50db81717e110bef6688c1186ffcb31348d5d00d27fe91eff070a1`.
The runtime was released.  The diagnostic alone did not retire
PRE-VALIDATION or move any counter or downstream orientation claim.

The single terminal workflow then cold-sealed the same immutable source in
GitHub Actions run `31917596890` (job `95092009512`, vehicle checkpoint
`c2a9dd7e2fb793838771f1fe995cf3bccf6c718f`).  Restore and save were both
skipped; focal/audit exited `0/0`; the focal ended with literal line
`Build completed successfully (8657 jobs).`; and all three audit blocks were
exactly `[propext, Classical.choice, Quot.sound]`.  `FINAL_STATUS=PASS`, all
`14/14` internal SHA-256 entries match, artifact id `9255750579` has GitHub
digest
`43811a374d17fb172bc22b5f23719f8876af9443fd88d017bf993ccfdeabde9f`,
and the downloaded evidence archive has SHA-256
`3276539b687868f7345109d9e2e64d4335717c77fc040e11fd3b967c3f8c1d31`.
PRE-VALIDATION is retired exactly for the source and audit certified here.
The orientation bridge remains open; counters stay `20/41`,
`TermSource = 0`, and window 15 remains compatible but unattained.

### Step 8b.14: stabilized column solution and literal endpoint sum (COLD-SEALED)

Source checkpoint `e3f613b66edea1ad7fc7fde472a2b4ac093a7c9e` adds
`BalabanCMP89Eq249StabilizedAliasColumnSolution` and its five-declaration
audit.  Source/audit Git-blob SHA-256 are
`0ea5db98dba245eb09bf12097a7f3e2f65810dc860d612254b618477af5330ab`
and
`2ef8189260419385af18bfd34ad0fb55e29886aae8a916d092cd816ced742fef`.

The brick constructs the direct-momentum column solution internally with the
same removable central cancellation as the cold-sealed transposed solution,
proves that it solves the original finite alias matrix, transports the
noncentral subtype sum to the literal raw-alias sum, and identifies the
complete phase-weighted column sum with
`cmp89Eq248ComplexStabilizedGreenEndpointIntegrand`.  No nonvanishing
hypothesis is needed for the endpoint identity itself; the inverse-system
theorem exposes exactly the noncentral and stabilized nonvanishing premises.

This is not yet the orientation bridge.  No equality between the physical
row sum of Step 8b.13 and this column sum is claimed, and no termwise
zero-alias preservation is smuggled through the affine carry.  Cross-fibre
Fourier-negation reindexing, Green periodization, regional `B0`, window-15
attainment, terminal-field production and `TermSource` habitation remain
open.  Both new files are visibly PRE-VALIDATION and NOT CHECKED; no Lean or
Lake ran on Windows.  Counters remain exactly `20/41`, `TermSource = 0`;
window 15 remains compatible but unattained.

Diagnostic runner checkpoint `7668978b71d900e2b9f85fefda30e39868dfb497`
has Git-blob SHA-256
`30bc97fc31ca432ff7bd94ad55b097378b59eea3eb776db3981d8c2def012f42`;
notebook vehicle checkpoint is `2d4c4ceb29e3a16c659fc68ec0623f436a0f29ee`.
Its Mathlib-only repro checks the finite central/erase split and common-factor
sum rewrite before the focal.  The runner fixes the source SHA and both Git
blob hashes, expects exactly five axiom blocks, stops on first error and
releases the runtime.  It authorizes one fresh-clone Colab diagnostic only;
PRE-VALIDATION remains until a later cold terminal seal.

The v1 diagnostic stopped at the first focal error after `879.818 s`:
`BalabanCMP89Eq249StabilizedAliasColumnSolution.lean:172:8` had the already
proved central pair in the opposite commutative order (`column * row` versus
`row * column`).  `FINAL_STATUS=FAIL`; evidence and archive SHA-256 are
`5e56b7d26ca44fa785e2a96799c4ef9c562ff1035b9ad3b8660d0f2ee8e55816`
and
`bcf9fda505f0015e01f3c5b9ef8964369e694940e36fb14d50501d1638141340`.
The runtime was released.  The v2 source changes only that multiplication
normalization; statements, constants, hypotheses and delimitations are
unchanged.  Corrected source checkpoint is
`5d3fab0e1d3513a5733ce525a05edb06a05731bf`; corrected source/audit Git-blob
SHA-256 are
`8f54dad29eb3040d0c59cd90eea693333cfe745f6c73d51175d16288247461df`
and
`2ef8189260419385af18bfd34ad0fb55e29886aae8a916d092cd816ced742fef`.
Step 8b.14 remains PRE-VALIDATION and NOT CHECKED pending v2.
Runner v2 checkpoint `b098b649275d64eb376de2a279b2636bc2c505fd`
has Git-blob SHA-256
`e7fa94d4347b5147364c6f4de1d07c1d65c54a5375e93142d4eee0c473f063c7`;
its notebook vehicle checkpoint is `4f835cd9`.  It preserves the same repro,
focal, five-block audit, stop-on-first-error and runtime-release contract.

Diagnostic v2 checked out exact corrected source
`5d3fab0e1d3513a5733ce525a05edb06a05731bf` in a fresh Colab Pro+ CPU/high-RAM
runtime with 50.99 GiB visible RAM.  The focal exited zero in `1263.399 s`
with literal terminal line `Build completed successfully (8495 jobs).`; the
audit exited zero in `10.400 s`.  All five declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`d0161493dba3c62ba11a82118c1201f857c49a0df4d940b621c5a50309256543`
and
`bab210969ff4e46cfde22358ec8931b20de41f7eb4ec29d58247921acbbf0071`.
`FINAL_STATUS=PASS`, launcher exit was zero and runtime release was requested.
This remains diagnostic evidence only: both PRE-VALIDATION marks and all hard
counters remain unchanged pending the single cold terminal seal.

The single authorized cold terminal workflow
[`31921457075`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31921457075)
(job `95101855543`, vehicle checkpoint
`c18f23c8f33ea8c097ef588ee943b2de3196c443`) checked out the same immutable
source.  `COLD_MODE=true` was recorded; project-graph restore and save were
both skipped.  Focal/audit exited `0/0`; the focal ended with literal line
`Build completed successfully (8495 jobs).`; all five audit blocks were
exactly `[propext, Classical.choice, Quot.sound]`; and the new-module warning
gate passed.  `FINAL_STATUS=PASS` and all `14/14` internal SHA-256 entries
match.  Artifact id `9256700099` has GitHub digest
`6d690b440aec4f0d9f9113f81f343134620837823b560ead80aa1d3f619e2229`;
the downloaded deterministic archive has SHA-256
`ffc8fb2bd352c1681f7a742a37382c1da05663e1d922333b0fd93eb209addc3a`.

This evidence retires exactly the source and audit PRE-VALIDATION marks for
Step 8b.14.  It seals the column solution and literal column endpoint sum,
not a row-to-column identity, Green periodization, cross-fibre reindexing,
regional `B0`, window-15 attainment, terminal-field producer or `TermSource`
inhabitant.  Counters remain exactly `20/41`, `TermSource = 0`; window 15
remains compatible but unattained.

### Step 8b.15: stabilized Green endpoint physical period (COLD-SEALED; orientation bridge open)

Source checkpoint `ce2522edfb26366dee93db84640dcff6298f141c` adds
`BalabanCMP89Eq248StabilizedGreenEndpointPeriodicity` and its seven-declaration
audit.  Source/audit Git-blob SHA-256 are
`9c1417e951a5e9fb29ed1431484a81e6570c8adcf91207df8e56c6caadf642ec`
and
`97f0d810895611def785ceb99335c282cd2b5c9e84b1a1da5c4f5ea8887db2e4`.

The brick deliberately does not assert that the central-stabilized
denominator is periodic.  It constructs the displayed rational Green sum,
proves its physical period by the already sealed centered-alias cycle, proves
displayed/stabilized equality on the complete non-singular domain, and only
then transports the period to the stabilized extension.  Integer endpoint
coordinates are data, so phase periodicity is derived internally.

This is not the physical orientation bridge.  No row/column equality,
cross-fibre Fourier-negation carry, termwise zero-alias preservation,
Brillouin integral, regional `B0`, window-15 attainment, terminal-field
producer or `TermSource` inhabitant is claimed.  Both new files retain visible
PRE-VALIDATION headers and are NOT CHECKED; no Lean or Lake ran on Windows.
Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains compatible
but unattained.

Diagnostic runner checkpoint `4992b07187f91dd25ad6f3cc6424711392c3c8c8`
has Git-blob SHA-256
`84550d722b55a58ae1041606ef0732844d3c0a511f7167d4cc3c3e082c4c0dd0`;
notebook vehicle checkpoint is `40b01b3fbe110aa4416ab12e76cbefdb7b7fb103`.
The runner fixes the immutable source and both Git-blob hashes, runs a
Mathlib-only central-split/common-factor repro, the focal and the seven-block
audit, stops on first error and releases the runtime.  It authorizes one
fresh-clone Colab diagnostic only; PRE-VALIDATION and hard counters remain
unchanged.

The fresh Colab Pro+ CPU/high-RAM diagnostic checked out exact source
`ce2522edfb26366dee93db84640dcff6298f141c` with 50.99 GiB visible RAM.
Runner/base-runner, source/audit blobs, Lean `v4.29.0-rc6` and Mathlib
`07642720480157414db592fa85b626dafb71355b` all passed their gates.  The
Mathlib-only repro exited zero in `14.875 s`; the focal exited zero in
`957.539 s` with literal terminal line
`Build completed successfully (8493 jobs).`; and the audit exited zero in
`8.731 s`.  All seven declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`28051de2d14fdb7c3cd7a48d27f0d3750413040c4deed1060ccd6ca4a4b1ec8e`
and
`d857d9bca0d919ffae4f3e87251ddfd7c0e928a75f4a84da1721c7e22fed4fa4`.
`FINAL_STATUS=PASS`, launcher exit was zero and runtime release was requested.
This is diagnostic evidence only: PRE-VALIDATION and counters remain pending
the single cold terminal seal.

The single authorized cold terminal workflow
[`31923477687`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31923477687)
(job `95107157525`, vehicle checkpoint
`37302a98472ddb6b9fd6fb2d7114d975ce902034`) checked out the same immutable
source with `COLD_MODE=true`; project-graph restore and save were both
skipped.  Focal/audit exited `0/0`; the focal ran
`03:09:00Z--03:27:26Z` and ended with literal line
`Build completed successfully (8493 jobs).`; all seven audit blocks were
exactly `[propext, Classical.choice, Quot.sound]`; and the new-module warning
gate passed.  `FINAL_STATUS=PASS` and all `14/14` internal SHA-256 entries
match.  Artifact id `9257341755` has GitHub digest
`8e1b8763d8fc79c73d06b1b61d141802f98395cf7d3cfb2c944925906f8b0126`;
the downloaded deterministic archive has SHA-256
`2ee75104e0703ee04ba4a8eebc0a5e7f4e9c2a00a10f9bef125fd0f6f6aa74a6`.

This evidence retires exactly the source and audit PRE-VALIDATION marks for
Step 8b.15.  It seals physical periodicity of the stabilized Green endpoint
on the stated non-singular domain, not a row/column identity, cross-fibre
Fourier-negation carry, termwise zero-alias preservation, Brillouin integral,
regional `B0`, window-15 attainment, terminal-field producer or `TermSource`
inhabitant.  Counters remain exactly `20/41`, `TermSource = 0`; window 15
remains compatible but unattained.

### Step 8b.16: alias-reflection coefficient transport (SEALED; coefficient substrate only)

Source checkpoint `e4d2b2eb6640d5c36d6febad8b424bdbd5c40c99` adds
`BalabanCMP99SourceAliasReflectionCoefficients` and its five-declaration
audit.  Source/audit Git-blob SHA-256 are
`593be2a9474c75b10e04c2f462a8d3ade70dac6903f2403e36a540318fd272fc`
and
`3e5259c476fcc0de4095cb06d722c529d57580ad4d24f6363701edc511618ee9`.

The brick does not identify the half-open centered reflection with literal
integer negation.  It derives coordinatewise divisibility from the sealed
`ZMod M` reflection law, constructs the resulting integer `2*pi*M` carry in
the alias momentum, and uses the already sealed exact period laws to exchange
the averaging column and row and to preserve the fine symbol.  Evenness of
the entire opposite-momentum Laplacian pairing is proved directly.

The stabilized denominator and solution, central-alias behavior, complete
cross-fibre finite-sum reindexing, Brillouin integral, regional `B0`, window
15, terminal field and `TermSource` remain open.  In particular no termwise
zero-alias preservation is claimed.  Both Lean files remain visibly
PRE-VALIDATION and NOT CHECKED; no Lean or Lake ran on Windows.  Counters
remain exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.


Diagnostic runner checkpoint `9a55678052e7c5394ef5c51f5de86f4ab9f8be14`
has Git-blob SHA-256
`b6de4efa8f7f20436fa95f9b36395278f3dd043862906ec78214b764f71adbc2`;
notebook vehicle checkpoint is `8b756f09d1051015ac283dea71b3403c7baca8af`.
The runner fixes the immutable source and both Git-blob hashes, runs a
Mathlib-only algebraic repro, the focal and the five-block audit, stops on the
first error and releases the Colab runtime.  It authorizes one fresh-clone
diagnostic only; PRE-VALIDATION and hard counters remain unchanged.

Fresh Colab diagnostic v1 ran once under visible account
`lluiseriksson@gmail.com`, CPU/high-RAM (`50.99 GiB`), from
`2026-08-16T03:36:09.403215Z`.  Transport, exact HEAD/blob gates, both text
guards, Lean `v4.29.0-rc6`, Mathlib
`07642720480157414db592fa85b626dafb71355b`, cache acquisition and the
Mathlib-only repro all passed.  The focal stopped at its first real error
after `1582.090 s`, before the audit, with three elaboration failures in the
new source: product normalization at line 70, rewriting beneath pointwise
negation at line 108, and `M^1` versus `M` at line 131.  Evidence/archive
SHA-256 are
`26c59972365ad22422e8ebffd2cedb0a7e50e5e0aea89f94e1b905223f426861`
and
`1e8e856ce993b0253cf556f02443426888db9be909b2f466091e09faefea4e89`;
`FINAL_STATUS=FAIL`, launcher exit was one and runtime release completed.

Source repair checkpoint `c669f5f5e081c316186bfbeade7a6a79752db418`
changes only those three proof normalizations; the theorem statements,
constants and hypotheses are unchanged.  Revised source/audit Git-blob
SHA-256 are
`e2675eb46f47dad3fa60d0d88e29edd3f62ba6c5c8dc9f04d250343446a915f7`
and
`3e5259c476fcc0de4095cb06d722c529d57580ad4d24f6363701edc511618ee9`.
Diagnostic runner v2 checkpoint
`ca4bf05623a5cbc47b98acf6754417b1c01c116a` has Git-blob SHA-256
`2b3fea3c0973da95cbe08f9be3ec6085eaafaae93b0b974640cc3e1962c0462c`;
notebook checkpoint is `e0bed88bbdd9a0b9383e82ed6549906188d0a11f`.
PRE-VALIDATION remains visible and the repair remains NOT CHECKED.

Diagnostic v2 stopped before the project focal: its newly added algebraic
repro was identically normalized by `ring_nf`, so its following
`linear_combination` produced `No goals to be solved`.  This is classified as
instrumentation failure, not source evidence.  Evidence/archive SHA-256 are
`eeda3592664f8857b22b596707b64eedfd0c4e04752ed4393c109dc9e0ec949c`
and
`9821f501f04d363cfd01afa90ff9876bb5b91e724afcb6cc10a8c1c941365ec4`;
the runtime released after `198.313 s`.  Runner v3 checkpoint
`616734a5dec1c50abcea0b3b70d4975718621038`, Git-blob SHA-256
`337d6f4984a4de4b51d2b06b8889e8071d16c11123dc1d0a33cb71cc0e2a13d2`,
replaces only that repro with the actual affine equality.  Notebook v3 is
`e455e56fc3534f318413322fe3af46e0ffdf0742`.  Mathematical source and both
source hashes remain unchanged; PRE-VALIDATION remains visible.

Diagnostic v3 ran exactly once in a fresh Colab CPU/high-RAM clone under
visible account `lluiseriksson@gmail.com`, opening at
`2026-08-16T04:44:12.355106Z`.  It verified exact source
`c669f5f5e081c316186bfbeade7a6a79752db418`, both blob hashes, Lean
`v4.29.0-rc6`, Mathlib `07642720480157414db592fa85b626dafb71355b`, both
text guards and the corrected repro.  The focal exited zero in `1472.330 s`
with literal terminal line `Build completed successfully (8542 jobs).`;
the audit exited zero in `9.529 s`; and all five declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`5fd5d3bd409275b336b53d2530f7dda57c938e5d7695b4b3ca19679960593ecc`
and
`5cc37f24880b34132f14aa695329af08e57dbf6b29d78fea4ac4e433c35b6015`.
`FINAL_STATUS=PASS`, launcher exit was zero and runtime release completed;
connected execution was `1667.939 s`.

This is diagnostic evidence only.  PRE-VALIDATION remains visible pending
the single cold seal.  Workflow vehicle checkpoint
`c3e6fa4787326e4cc671a09a637864a173277dae` has Git-blob SHA-256
`9bf5f25938bebf985fca562f585bebe80bc0f414ba874c232906d9cecdad0675`;
it fixes the same source and blob hashes, uses `cold=true`, skips project-graph
restore/save, and gates the five-declaration audit.  No terminal workflow has
yet been dispatched for this vehicle.

Terminal cold GitHub Actions run
[`31928676798`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31928676798),
job `95120140347`, then sealed exact source
`c669f5f5e081c316186bfbeade7a6a79752db418` from workflow HEAD
`f5c652d7c07105b7e91ecb0c9348151bebfd85ef`.  It recorded
`COLD_MODE=true`; project-graph restore and save were both `skipped`.
The focal ran from `2026-08-16T05:19:44Z` to `05:42:28Z`, exited zero and
ended with literal line `Build completed successfully (8542 jobs).`; the
audit ended at `05:42:35Z` with exit zero.  All five declarations printed
exactly `[propext, Classical.choice, Quot.sound]`.

The downloaded artifact has id `9258894150` and GitHub digest
`sha256:40ccf09bd2ad87e80344881e340e7a8a67caaefe1c080814177c95f27ee1c788`.
Its `14/14` internal SHA-256 entries verified, and the deterministic local
archive SHA-256 is
`762a166bb55689cd897532efb2d6533c5908d38eebdbc6526a730542b859a21f`.
This cold evidence retires exactly the source and audit PRE-VALIDATION marks.
It seals coefficient algebra only: stabilized denominator/solution,
central-alias termwise behavior, complete cross-fibre physical reindexing,
Brillouin integral, regional `B0`, window 15, terminal fields and
`TermSource` remain open.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.

### Step 8b.17: reflected stabilized denominator and solution (COLD-SEALED; physical cross-fibre bridge open)

Source checkpoint `ce00198eb10766b15e3fb90dc756cbf634e34740`
(second proof-only repair of initial checkpoint
`e215af32bd506bfc27604b55f6791e750fa1242a`) adds
`BalabanCMP99SourceAliasReflectionStabilizedSolution` and its
seven-declaration audit.  Source/audit Git-blob SHA-256 are
`0925f929542853a1826bd61dbeed67ccb2679b4679ac328c8ba8e7e2746b9591`
and
`579d4b8ea2d6988528c66fc19aeec46c3565a5dd77f8ea386c653c8184ffc61d`.

The source composes the sealed coefficient reflection on the complete CMP89
depth-one alias fibre.  It proves that the actual half-open residue
reflection fixes the central alias, reindexes the noncentral rational sum,
preserves the central-stabilized denominator, and transports the stabilized
transposed solution at opposite base momentum to the direct-momentum column
solution.  These conclusions are constructed internally; no denominator
symmetry, solution family, nonvanishing premise or finite-sum identity is
accepted from the caller.

This brick remains below the physical cross-fibre bridge.  It does not
identify the affine carry from `ell` to `cmp99FinBoxFourierNeg ell` with the
simple alias reflection, preserve the zero alias termwise under that carry,
reindex the complete physical endpoint sum, construct a Brillouin integral
or regional `B0`, attain window 15, discharge a terminal field or inhabit
`TermSource`.  At the initial source checkpoint both Lean files retained
visible PRE-VALIDATION headers and were NOT CHECKED; no Lean or Lake ran on
Windows.  Counters remain exactly
`20/41`, `TermSource = 0`; window 15 remains compatible but unattained.

Diagnostic v1 on initial source `e215af32...` passed transport, pin and
Mathlib-only gates, then stopped at the focal after `1314.206 s` with exit
code `1`; the audit did not run.  Evidence/archive SHA-256 are
`c3a186f604049c3cd3a123ccfcd3a44a175a419d30966880a2cbe812bf897748`
and `e10a04a2b73d0aef5438313733b54cb79b1635c9bb5169b28f636f691e5721a0`.
The only errors were three elaboration normalizations: residue zero after
the equivalence, `M ^ 1` before the fine-symbol evenness lemma, and rewriting
the reflected central alias before the row/column coefficient theorem.  No
statement, hypothesis or constant changed in checkpoint `53d03123...`.

Diagnostic v2 on source `53d03123...` passed every preflight and the two
nonzero repairs, then stopped at the focal after `1539.035 s` with one
remaining elaboration error: `change` could not unfold the residue
equivalence at the distinguished zero alias.  The audit did not run.
Evidence/archive SHA-256 are
`4916a7c0e385a54d459733c8784b73684e12cb0cb9fa87a149bbe071e0037b06`
and `6147896078549ad08585966c7bf3cdc32bd55b41692ff12ce2f623935772bf93`.
Checkpoint `ce00198e...` replaces only that failed definitional conversion
with the already sealed exact application theorem.

Diagnostic v3 runner checkpoint
`b7e12fa9d682f7f87e22a23e7374817050c68310` has Git-blob SHA-256
`69dd7b40af713b5bce658c0282198cf2b20c14fb434827e01afc7265cc6058a0`;
notebook vehicle checkpoint is
`31336112d0a30e7f520c90553a7d8cce8289870b`, with Git-blob SHA-256
`b54bf75d3986fa294459959d79c6887c44b9f1164b24e4050813070ab536acbc`.
The runner gates exact source and both source blobs, executes a Mathlib-only
reproduction of the finite-sum reindex-and-erase argument, then runs the
focal and seven-block audit stop-on-first-error in one fresh Colab CPU/high-
RAM clone and releases the runtime.  It authorizes one diagnostic only and
does not retire PRE-VALIDATION or move a counter.

Diagnostic v3 ran exactly once in a fresh Colab Pro+ CPU/high-RAM clone under
visible account `lluiseriksson@gmail.com`, opening at
`2026-08-16T07:36:35.847150Z` with `50.99 GiB`.  It verified source
`ce00198eb10766b15e3fb90dc756cbf634e34740`, both blob hashes, Lean
`v4.29.0-rc6`, Mathlib `07642720480157414db592fa85b626dafb71355b`,
both text guards and the Mathlib-only repro.  The focal exited zero in
`1149.297 s` with literal terminal line
`Build completed successfully (8590 jobs).`; the audit exited zero in
`7.851 s`; and all seven declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`31bbd47b8cd7a8b575125fa6bbe29374b49c331c674d647fe8aa0b3df9a11e67`
and `e42f6a070e86f50526d942ee02027dc3753db0679e636ac6f027f5e7a0431c98`.
`FINAL_STATUS=PASS`, launcher exit was zero and runtime release completed;
connected cell time was `1272.875 s`.

This is diagnostic evidence only.  PRE-VALIDATION remains visible pending
the single cold terminal seal.  Workflow vehicle checkpoint
`efb75529f1359ebe7457997d37d4d75693e701f2` has Git-blob SHA-256
`9dc86518ccf4bcd8b81bbb2fc10639cfe11a2ae5d616b9c6828f37e73725acf6`.
It pins the same immutable source and blobs, requires `cold=true`, skips
project-graph restore/save, runs focal then seven-block audit, rejects
new-module warnings and packages deterministic evidence.  No terminal run
has yet been dispatched.

The single terminal cold GitHub Actions run
[`31935700856`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31935700856),
job `95137148615`, checked out exact source
`ce00198eb10766b15e3fb90dc756cbf634e34740` from workflow HEAD
`1336cf08eb8e2a6e731a83615cd40f77cefef6da`.  It recorded
`COLD_MODE=true`; project-graph restore and save were both `skipped`.  The
focal ran from `2026-08-16T08:11:20Z` to `08:34:26Z`, exited zero and ended
with literal line `Build completed successfully (8590 jobs).`; the audit
ended at `08:34:32Z` with exit zero.  All seven declarations printed exactly
`[propext, Classical.choice, Quot.sound]`, and the new-module warning gate
passed.

The downloaded artifact has id `9260879647` and GitHub digest
`sha256:021bdca07c722250400c9cab8ee9296138b5d583101614b285abf800c268e83e`.
Its `14/14` internal SHA-256 entries verified, and the deterministic archive
SHA-256 is
`4fae14dc8b51ec5990987057481e2b5a89d8986463c71deab2b8f59bff9dd87b`.
This cold evidence retires exactly the source and audit PRE-VALIDATION marks.
It seals simple alias-reflection algebra only, not the affine cross-fibre
physical sum, Brillouin integral, regional `B0`, window-15 attainment,
terminal fields or `TermSource`.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.

### Step 8b.18a: stabilized-to-quotient bridge (COLD-SEALED)

Source checkpoint `01f9a0c287666094233343e4bd63a4edc8224bdb` adds
`BalabanCMP99SourceStabilizedAliasQuotientBridge` and its five-declaration
audit.  Source/audit Git-blob SHA-256 are
`cb44411e518726f2fe74e3f6ee3f76432c6de582b188eefaf199ff3d40f93c04`
and
`8d2f7f222bb824e08ceae8adf4293418f4ca9c5fede3d7a85f48758ef1625647`.
Both Lean files retain visible PRE-VALIDATION headers and are NOT CHECKED;
no Lean or Lake ran on Windows.

This brick proves two facts needed before the affine physical reindexing.
First, the complete reduced denominator is even under the actual half-open
alias reflection and periodic under coordinatewise integer physical periods.
Second, on the full non-singular domain, both separately constructed
central-stabilized solutions cancel exactly to their literal rational
quotients.  The nonvanishing hypotheses remain visible and are not inferred
from stabilization.

The scope is deliberately coefficient-level.  It does not assert periodicity
of the central-stabilized denominator, identify the affine carry between
coarse Fourier fibres, preserve the central alias termwise under that carry,
transport endpoint phases, reindex the complete physical sum, construct a
Brillouin integral or regional `B0`, attain window 15, discharge a terminal
field or inhabit `TermSource`.  The zero and nonzero coarse fibres remain a
required split for the later physical bridge.  Counters remain exactly
`20/41`, `TermSource = 0`; window 15 remains compatible but unattained.

Diagnostic v1 stopped at the source-blob gate before dependency
materialization, the Mathlib-only repro, focal or audit.  The expected source
digest had lost the two hex characters `af`; the actual Git blob remained
unchanged and verified as
`cb44411e518726f2fe74e3f6ee3f76432c6de582b188eefaf199ff3d40f93c04`.
The same static review also found that the optional repro's right-hand side
used the wrong cancelled factor.  This is `BLOCKED-INSTRUMENTATION`, not
compiler evidence.  `FINAL_STATUS=FAIL`; evidence/archive SHA-256 are
`68ae4c6835d5174e02d2f13654cac3331c83fe5c2786314559b3a3828a3cb969`
and
`56a5520421543389ef9ca00d588c97df36a8e4335396d19d66caec6ac8630fbf`.
The Colab CPU/high-RAM runtime released after `52.473 s` and the tab was
closed.  v2 changes only those two runner constants; mathematical source,
statements, hypotheses and source checkpoint remain unchanged.

Diagnostic v2 then passed transport, both corrected source-blob gates,
toolchain/Mathlib pins, both text guards and cache materialization.  Its
corrected algebraic equality was discharged completely by `field_simp`, so
the following standalone `ring` failed with literal error
`No goals to be solved`.  Stop-on-first-error prevented the project focal and
audit.  This is again `BLOCKED-INSTRUMENTATION`, not source evidence;
`FINAL_STATUS=FAIL`.  Evidence/archive SHA-256 are
`1723241b88e646cee6350234d9914deca53f940baae7129170a58927a4454b01`
and
`c2b89b2404f90c135938921cfa217ff7326efb65ff0ede8b9ee8823e9554cdf1`.
The runtime released after `160.571 s` and the tab was closed.  v3 replaces
the repro by the literal stabilized-to-reduced quotient equality and uses
`field_simp [...] <;> ring`; mathematical source remains unchanged and
PRE-VALIDATION remains visible.

Diagnostic v3 passed all transport, blob, pin, text and Mathlib-only repro
gates, then reached the project focal. It stopped after `1819.971 s` with
exit code `1`; the audit did not run. Both errors were the same literal
residual cancellation in the row and column branches:
`centralFine * coefficient * centralFine⁻¹ = coefficient`.
Evidence/archive SHA-256 are
`d8734490b613a8490123336d1ba8b9afd91190c65d329804103e7d58803b2901`
and
`87b08b05a0d19bcd5d9f95b96b0c8ef75af69edb07f6563d31b793b1833fbade`.
The runtime released and the tab was closed.

Repair checkpoint `839727ffa9b21fd683c23558dac0211374cefdd8`, source
Git-blob SHA-256
`97d4780f50271eec24c1df523f49e0439056181338c3a044c5b1ea7ea824b67e`,
changes only those tactic tails to explicit commutation, association and
`mul_inv_cancel₀ hcentral`. Runner v4 checkpoint
`756a7a41bd65597b756fe3e550f230cdc3df7ef8`, Git-blob SHA-256
`19b4415bdd29f81a45d158f38bb8006cce53ba4b6d148f75dcde17b3708c68ff`,
and notebook checkpoint `acd5bd0ef4491f659ada880e9c32253225d3f322`,
Git-blob SHA-256
`750bbfce89ce5510011b3936ac098645697c8fc893f886472f02d7d661e7a81b`,
test that exact residual shape before the focal. No statement, hypothesis,
constant or scope changed. PRE-VALIDATION remains visible and the result
remains NOT CHECKED; counters remain exactly `20/41`, `TermSource = 0`, and
window 15 remains compatible but unattained.

Diagnostic v4 stopped before the project focal. It passed transport, repaired
source/blob hashes, pins, text guards and cache materialization, but its
abstract quotient repro was already closed by `field_simp`; the following
rewrite failed with literal `No goals to be solved`. Evidence/archive
SHA-256 are
`cdb4c9fa228dbc7e94ebd4fa08dc68b6075ffcba3b0a8172684f36bef176d559`
and
`79654d9050d7c014c61bbb08656cb34f4f154dd817c59695de88a78279150168`.
The runtime released after `114.682 s` and the tab was closed.

Runner v5 checkpoint `17dfd10ac96e8d14821eef006c1ab34cc9276dc2`,
Git-blob SHA-256
`1fb81b491e327b74910e0944d5c2323017afbe2090175e201923160c7230c757`,
tests only the exact residual cancellation. Notebook checkpoint
`4c9857bca0c168bbe8b228720035770e2b6527fd`, Git-blob SHA-256
`de978d372f05a4b566b87b001abae12d1525441bbdb69fb5d86f96f8d9498dd6`,
pins it. Source remains `839727ffa9b21fd683c23558dac0211374cefdd8`;
PRE-VALIDATION remains visible, the result remains NOT CHECKED, and counters
remain exactly `20/41`, `TermSource = 0`, with window 15 compatible but
unattained.

Diagnostic v5 passed every preflight and the exact residual-cancellation
repro, then reached the source focal. It stopped after `1125.846 s` with
exit code `1`; the audit did not run. The two source failures had the same
precise shape:
`coefficient * centralFine / cmp89Eq249CentralEntireFineSymbol … =
coefficient`. Evidence/archive SHA-256 are
`fb468cd86d8088850ab1dec99f882a8fa9a17adf7dde3c233bdb665e7b83719e`
and
`890aeddabedc32e8d786528c180be82d97ccbd7e78ce3d3aa4392001da0005ab`.
The runtime released after `1248.462 s` and the tab closed.

Repair checkpoint `64714dc87b9aecec8af7a3418eeab6258a3b823c`, source
Git-blob SHA-256
`b050fde2d0270936e15e82b6b3439ef56fe7673612413d70a1563d8b7648943a`,
makes the definitional denominator `centralFine` visible and then clears the
literal quotient with `hcentral`. Runner v6 checkpoint
`9cdd6968f5ff51638cb96a21d2552889cb49d35d`, Git-blob SHA-256
`c8c82229f68f9acfb029f73cfcb50d3f2748e4b03626ca21b56fbb1576840b14`,
and notebook checkpoint `e4a958eb175b478fbf647ccaa902ead4aae6ef85`,
Git-blob SHA-256
`2adb85d203fa81cba4a1750e65a4c9f3eb686425d9a12363b8a81a4128c49a7c`,
pin that exact residual repro. No statement, hypothesis, constant or scope
changed. PRE-VALIDATION remains visible and the result remains NOT CHECKED;
counters remain exactly `20/41`, `TermSource = 0`, and window 15 remains
compatible but unattained.

Diagnostic v6 passed every gate and the exact quotient-cancellation repro,
then reached the focal. It stopped after `1117.935 s` with exit code `1`;
the audit did not run. Lean rejected the same whole-goal definitional
`change` in the row and column branches: the literal central fine-symbol in
the target did not convert to the local `let` abbreviation. Evidence/archive
SHA-256 are
`1668b0c1ee7d45536f492e835b3f6d1fcc41248cfa20b8aaf07c4c7994d94a60`
and
`82fb7eb88717ee9c603bdc31b0c4303cb296965a075908305972c4f138ea302a`.
The runtime released after `1228.658 s` and the tab closed.

Repair checkpoint `c7bfde5edb48a52032d2616c7b15bf3ee753704d`, source
Git-blob SHA-256
`361f61fdce19b545ffea727453da58f7877249ef3f458d798303fdaaf58889ac`,
names nonvanishing of the literal denominator by simplifying the local
abbreviation, then cancels without converting the whole goal. Runner v7
checkpoint `1a2b3731a7f63be4c21910aaa58414d15872d66e`, Git-blob
SHA-256
`031d1f43d5c078a3375b43fb25600320e9bf39ffb012f2b6c504ea990c49267c`,
and notebook checkpoint `245f5063f2263ec11daaf096e179c4a0281e13d1`,
Git-blob SHA-256
`63ecea50e3234db2e4ed7c53d0d95e61a6526470faec3b97228a863a2064e99d`,
pin v7. Statements and scope are unchanged; PRE-VALIDATION remains visible,
the result is NOT CHECKED, counters remain `20/41`, `TermSource = 0`, and
window 15 remains compatible but unattained.

Diagnostic v7 passed every transport, blob, pin, text and Mathlib-only repro
gate, then reached the project source. The focal stopped after `1567.077 s`
with exit code `1`; the audit did not run. In the row and column noncentral
branches, the first denominator-clearing `field_simp` already closed the
goal, so each following tactic line failed literally with
`No goals to be solved` (lines 155 and 193). Evidence/archive SHA-256 are
`0caf0e09a7016b28ec4f8748f52a766f41afcc0cb5af8f7317e839588c0ef94e`
and
`227608e7ff8fa2c09ac6071865fffd9a444be83c902eda8bae255b16eebf83f0`.
The runtime released automatically after `1716.492 s` and the tab closed.

Repair checkpoint `fc26d50d2c660a26b65c1e3bbf79e8761b35b4da`, source
Git-blob SHA-256
`268f6f985af57ccbb7013a5951f0276d6d6595599d65986d3c02a50a3a2c5cba`,
removes only those redundant tails and their unused local literal
nonvanishing names. Runner v8 checkpoint
`94cf85a966b3b98bb9e0200fdaa0b6df546a79f5`, Git-blob SHA-256
`5624cbba3ec2894bf12cc35d034a3675b54053781c4308dd1a1bc795a0d50ab3`,
and notebook checkpoint `ab0b022356669b33532d292ce891dc53ce609d28`,
Git-blob SHA-256
`a153554868535e713fccd63b5b5ef2d0719ee76f1fc8e4081f536d1b7c3200e6`,
pin v8. Statements, hypotheses, constants and scope are unchanged;
PRE-VALIDATION remains visible and the result remains NOT CHECKED. Counters
remain exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

Diagnostic v8 passed every transport, blob, pin, text and Mathlib-only repro
gate, then reached the project source. The focal stopped after `1625.516 s`
with exit code `1`; the audit did not run. Its only two goals were the literal
row/column instances of
`centralFine * coefficient / centralFine = coefficient`. Evidence/archive
SHA-256 are
`0c2228f831b35cedbde9f1dddec8e3d8851714c0f05f7eeb41b4a375b82c8f36`
and
`95a51925a03e0774f8a1215d29d807e7dc69211dbd3f659269c982b75e25bde5`.
The runtime released after `1780.514 s` and the browser tab closed.

Repair checkpoint `72e665f18309e7fb96c4bc720b52296a03fabecc`, source
Git-blob SHA-256
`5638e4b31785fafabd591e0a9c8bab4cb19d138fd789c4d4c6aaae0d999c7167`,
adds only the standard `mul_div_cancel_left₀` rewrite to those two exact
goals. Runner v9 checkpoint `7c2e79e515bdea59bd2c68fcc7f87fd9b7869ccd`,
Git-blob SHA-256
`8d33d3e586643edd6021f6ec5e678daf1add23f766a3007c9e5ccd97e787d6d2`,
and notebook checkpoint `860950fa5c053dcef2ca5461e66dcbd3d47a0ea0`,
Git-blob SHA-256
`5c046e11574e02b963848d54a4dc3bf33115c7325f1bf9308f1e1cf4a50a97bd`,
pin v9 and test the same cancellation lemma before the focal. No statement,
hypothesis, constant or scope changed. PRE-VALIDATION remains visible, the
result remains NOT CHECKED, counters remain exactly `20/41`,
`TermSource = 0`, and window 15 remains compatible but unattained.

Diagnostic v9 ran once in Colab Pro+ CPU/high RAM under the visible account
`lluiseriksson@gmail.com`. The first click was blocked by Colab's GitHub
security dialog and is classified as a non-start; the evidence clock began
only when runner v9 printed `STAGE=runtime_open` at
`2026-08-16T12:23:09.549075Z`. Exact transport, source/blob hashes,
toolchain/Mathlib pins, text guards and the direct
`mul_div_cancel_left₀` repro all passed. The focal then printed
`Build completed successfully (8591 jobs).`; all five audit declarations
printed exactly `[propext, Classical.choice, Quot.sound]`.
`FINAL_STATUS=PASS`; evidence/archive SHA-256 are
`9e05709a86014e20793c158b8c04c376fa48c335d1d6a31d3c0a33708fce57d9`
and
`03f4f6c8887d9772b72c64e281547c8bd4c214446aef12cbafbc402dbb4e59b5`.
The runtime auto-released after the run and the browser tab was closed.

Cold terminal GitHub Actions run `31948322330` then checked out exact source
`72e665f18309e7fb96c4bc720b52296a03fabecc`; both cache restore and save
were skipped. The focal again printed `Build completed successfully (8591
jobs).`, the five-declaration audit again printed exactly the standard axiom
trio, and `FINAL_STATUS=PASS`. The downloaded durable archive SHA-256 is
`4fff4812f17f07a993479411ed1cda12c154a5aa23889f2e612c1ae09147697c`,
matching its internal manifest. Seal commit
`dabe90ca5051996fe57a9fef669d3f607bd82324` retires exactly the two
PRE-VALIDATION marks. This seals parity/periodicity of the reduced
denominator and stabilized-to-literal quotient cancellation only; the affine
cross-fibre carry, complete physical sum, regional `B0`, window 15 and
terminal fields remain open. Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.

### Step 8b.18b: nonzero cross-fibre physical quotient transport (SEALED)

Source checkpoint `6fefea5306d8b1f8af470ea537c51954dd87fee4` adds
`BalabanCMP99SourceFlatQprimeCrossFibreAliasQuotient` and its
eight-declaration audit. The brick keeps the affine signed-alias carry
literal: periodic Fourier negation moves the physical fibre over `ell` to
the fibre over `FourierNeg ell`, and the row quotient becomes the column
quotient there. It derives reduced-denominator nonvanishing internally on
each nonzero coarse fibre from the sealed stabilized product and central
fine-symbol nonvanishing. It does not reflect a fixed physical fibre or
cancel the central mass-zero symbol.

Diagnostic v1 ran once in a fresh Colab Pro+ CPU/high-RAM clone under the
visible account `lluiseriksson@gmail.com`. Exact runner/source/blob gates,
official Lean/Mathlib pins, both text guards and the Mathlib-only repro
passed. The focal stopped with exit code `1` after `1639.397 s`; the audit
did not run. The three first errors were elaboration boundaries only:
`Nat.cast_sub` remained unapplied in the periodic representative,
pointwise function negation was not syntactically exposed to the sealed
denominator-evenness theorem, and the zero value of transported Fourier
negation was not supplied to the involution proof. `FINAL_STATUS=FAIL`;
evidence/archive SHA-256 are
`9995f5e0efa8d9a39dc41ea0ff9e9aea34af1940c9182ac0bdd9f0264173f070`
and
`60cf0bd3696fe4fd94c0b2d6c884107877b5009a6042fc1fbea3b25153f58a30`.
The runtime released automatically.

Repair checkpoint `316f9fab920a1ec9b6fead040e9d8dae16f19f4e`, source
Git-blob SHA-256
`2dd35012b5320e599f556f7f3e69d6299c253b666d6af107fc4d3ac168348ea9`,
applies exactly those three transports; statements, hypotheses, constants
and scope are unchanged. Runner v2 checkpoint
`de5d9688b1e89a0d2953731f832f0a05d299d644`, Git-blob SHA-256
`27a7e942b457282993cb3305515476a4cec63723abe2e7dddfc0351832d25b8e`,
tests the exact natural-subtraction cast before the focal. Notebook
checkpoint `e4c0b3a98a7901279075e47a2c6e48ae68c20c1b`, Git-blob SHA-256
`cd0b0f2ec929382a2f7e0152577b2e4ce697c0721f81cc05566597939df617bd`,
pins v2. PRE-VALIDATION remains visible and v2 is NOT CHECKED. The complete
finite alias sum, the zero coarse fibre, Brillouin integral, regional `B0`,
window 15 and terminal fields remain open. Counters remain exactly
`20/41`, `TermSource = 0`; window 15 remains compatible but unattained.

Diagnostic v2 ran once in a fresh Colab Pro+ CPU/high-RAM clone under the
same visible account. All transport, source/blob, pin, text-guard and repro
gates passed. The focal stopped with exit code `1` after `2019.806 s`; the
audit did not run. The only error was the remaining pointwise normalization
`-(fun mu => 0) = fun mu => 0` inside the proof that Fourier negation fixes
zero. `FINAL_STATUS=FAIL`; evidence/archive SHA-256 are
`f03a3b3122e853bc32541d3a5262106a7550d5382c9e97c761bbc44f315c3428`
and
`b463cb034b2f78ad587e46811fdf2b6cf3c664856b5342cc9f04f0a41be21a67`.
The runtime released automatically.

Repair checkpoint `da7eed698c279304d24fb7f7a5f64278cbededf0`, source
Git-blob SHA-256
`8b6f5296d06ab284a1bc15313797bd995a92d136791d3d0b4cbae492e89e0897`,
adds only pointwise function extensionality at that goal. Runner v3 checkpoint
`ae6ce9cf1a022e54d0a43bd52c0caa74372717d2`, Git-blob SHA-256
`3c0a137600a34dc4d25e9efcefb9e2172193586d710c5d9d7149b39e36e15caf`,
adds the exact Mathlib-only zero-function-negation repro. Notebook checkpoint
`f27bf31e72741f01d18557a79e8d7af92af38c51`, Git-blob SHA-256
`6f48e50df47f62458fa5045633e05214c735d0d9c8c988d1edb449abf354f1d9`,
pins v3. Statements, hypotheses, constants and scope are unchanged.
PRE-VALIDATION remains visible and v3 is NOT CHECKED. Counters remain exactly
`20/41`, `TermSource = 0`; window 15 remains compatible but unattained.

Diagnostic v3 then passed once in a fresh Colab Pro+ CPU/high-RAM clone at
exact source `da7eed698c279304d24fb7f7a5f64278cbededf0`. The repro passed;
the focal returned exit code `0` after `1861.516 s` with literal terminal line
`Build completed successfully (8631 jobs).`; the audit returned exit code `0`
after `13.046 s`, and all eight declarations printed exactly
`[propext, Classical.choice, Quot.sound]`. Evidence/archive SHA-256 are
`83978bc315339ca4e2301ed54d87be50589412ecf7c3aa319db2c10112e2acd4`
and
`b6e5912c41c0d628da311f9e3f8dae0640b528ad123fa12851f48715b62d1d9d`;
`FINAL_STATUS=PASS` and the runtime released automatically.

The single terminal cold workflow run `31956044339` at workflow checkpoint
`3b518600bc2237d4f28922df05246f78f8bd92cd` checked out the same exact source,
recorded `COLD_MODE=true` with project-cache restoration skipped, and passed
the focal/audit queue with exit codes `0/0`. It reproduced the same literal
`Build completed successfully (8631 jobs).` line and the same eight standard
axiom triples. The downloaded durable archive SHA-256
`08ab432aee6e21ea46a2be875f1ded9c933c75836d1d7c103fea3a1075f0171e`
matches `evidence/ARCHIVE_SHA256`; all `14/14` internal evidence hashes match
and `FINAL_STATUS=PASS`. Seal commit
`56e2b5418e9ac85ed9e9c2e87c61e3a4467be828` retires exactly the source and
audit PRE-VALIDATION marks.

The seal covers the nonzero-coarse-fibre affine Fourier-negation carry and
the transported literal stabilized row-to-column solution. It does not cover
the zero coarse fibre, the complete finite alias sum, a Brillouin integral,
regional `B0`, window-15 attainment or any terminal field. Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

### Step 8b.19: nonzero cross-fibre endpoint phase and complete physical-fibre reindexing (SEALED)

`BalabanCMP99SourceFlatQprimeCrossFibreEndpointPhase` separates the endpoint
phase from the mass-zero singularity.  Physical Fourier negation moves a mode
from the fibre over `ell` to the fibre over `cmp99FinBoxFourierNeg ell`; the
full `2*pi*M` alias period is discharged at the physical fine-lattice
displacement before moving the remaining sign from momentum to displacement.
The resulting pointwise identity is composed with the sealed Step-8b.18b
nonzero quotient transport and then reindexed over the complete finite
physical fibre.

This source deliberately assumes `ell != 0` only where the quotient solution
is consumed.  It does not assert that a distinguished alias is preserved
termwise.  The zero coarse fibre remains a separate branch to be discharged
with the sealed Eq. (249) reflection rather than quotient cancellation.  A
Brillouin integral, regional `B0`, window-15 attainment, terminal fields and a
`TermSource` inhabitant remain open.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.

Diagnostic v1 ran once in a fresh Colab Pro+ CPU/high-RAM clone at exact
source `dbd02a992c749b08e100a3b0b9258bb32a864924`.  Transport, source/blob,
pin, text-guard and Mathlib-only repro gates passed.  The focal stopped with
exit code `1` after `1642.968 s`; stop-on-first-error prevented the audit.
The two errors were explicit: the physical scale `M` remained a metavariable
at the alias-period lemma, and the pointwise consumer attempted to rewrite
the endpoint phase in the opposite orientation.  Evidence/archive SHA-256
are `8296115ef907eb2393d80800a3b9ffd00b1e437747edd5f3b47a3357efa4e846`
and `d57470d50979e8d630a0f26826f75979882673854bc6c6acd3ab5dc2aa44059e`.
`FINAL_STATUS=FAIL`; the runtime released automatically and the cell was not
rerun.

Repair checkpoint `237f11941c763e1a68071c2d69bc246d305dbb81`, source
Git-blob SHA-256
`c95973adaaef8717db6fe12360297a807c11d946ec13b2d1db5a3e6c2a439730`,
pins `(N := M)` and derives a separately typed equality
`phase_original(u) = phase_fourierNeg(-u)` before composing the two factors.
Runner v2 checkpoint `a4dad78a62574d156c8e9273c83621407dfe1c20`, Git-blob
SHA-256
`144148ee9472ada530196c58ad52ec38639f20c4912da9fa0a5b30df8d40ec6a`,
and notebook checkpoint `8513f4898ee818711bc05e909cbdec6b6dd6e4aa`, Git-blob
SHA-256
`67a9d731ad80fbd8dae1d1256aa7acb7fc7d0356f8e602e79f84340ae4f6a3ef`,
prepare the controlled retry.  Statements, hypotheses, constants and scope
are unchanged.  PRE-VALIDATION remains visible and v2 is NOT CHECKED.

Diagnostic v2 passed the same gates and stopped at the focal with exit code
`1` after `2143.029 s`; the audit did not run.  The explicit scale was now
correct, but the target exposed `(-p) mu` as `-p mu`, and the sample had
already unfolded the physical stabilized-solution wrapper before its sealed
theorem was applied.  Evidence/archive SHA-256 are
`2fc0ac994fd1e9fb408d822fac74caa23026a8219051b946e6e6f6e57ee2eb25`
and `eb3e8cd83bfcefd774c9572d64b137f224f548686594eb52e1e583a518fe21c2`.
`FINAL_STATUS=FAIL`; the runtime released automatically and the cell was not
rerun.

Repair checkpoint `affa623b62d9238e1f64f6c8ca87cfb76444c266`, source
Git-blob SHA-256
`c5f1893c0f95688701174e6ead237e38f374c716c3e4c44f6e273cc1960c5d80`,
uses an explicit `calc`/`Pi.neg_apply` conversion for the phase and a named
equality that unfolds the physical solution wrapper before factorwise
composition.  Runner v3 checkpoint
`c182cb6e3d10ad56769d7b022cd4a5ba478cd629`, Git-blob SHA-256
`3ec37b0974dda562d4ed9a5588287c4791e0542260315e17ab0bce6c9c296b3e`,
and notebook checkpoint `3014cd17165da45e8f8767728d32cd3414408fe9`, Git-blob
SHA-256
`5f9bf018dda4d032263b43b8fffa536a453accad33b8e5205b45204d13003643`,
prepare v3.  Statements, hypotheses, constants and scope remain unchanged;
PRE-VALIDATION stays visible and v3 is NOT CHECKED.

Diagnostic v3 passed once in a fresh Colab Pro+ CPU/high-RAM clone at exact
source `affa623b62d9238e1f64f6c8ca87cfb76444c266`.  All transport,
source/blob, pin, text-guard and repro gates passed.  The focal returned exit
code `0` after `1588.597 s`, with literal terminal line
`Build completed successfully (8701 jobs).`; the audit returned exit code `0`
after `8.898 s`, and all four declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`9ddf24ee25176d6898ae645e3105f853bda9c964db150271ab77c355903ee1dd`
and `3dd8be3b88970c9303e3d9a7d716ba34076aeeb8d905f06e48ad1a6f9c82aa3f`.
`FINAL_STATUS=PASS`; the runtime released automatically and the cell was not
rerun.  The seal retires exactly the two Step-8b.19 PRE-VALIDATION marks.

### Step 8b.20: zero-coarse-fibre endpoint reflection (SEALED)

`BalabanCMP99SourceFlatQprimeZeroFibreEndpointReflection` treats the singular
coarse fibre without dividing by the central mass-zero symbol.  It reindexes
the complete signed alias carrier by the sealed Eq. (249) reflection, moves
the endpoint phase to the opposite fine-lattice displacement using the full
physical alias period, and identifies the resulting finite sum with the
literal stabilized CMP89 column endpoint integrand.

The branch does not identify an affine cross-fibre carry termwise with the
reflection and does not cancel a central quotient.  Source and audit retain
visible PRE-VALIDATION headers; no Lean, Lake or oracle has run for this brick
on Windows.  The import-prefix and exact-overlay text guards pass over exactly
the two new files, but this is not compiler evidence.  A combined zero/nonzero
consumer, Brillouin integration, regional `B0`, window-15 attainment,
terminal fields and a `TermSource` inhabitant remain open.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

Source checkpoint `34f75aa60e39301a7fd281054513bfce5fe99cc2`
contains the immutable two-file brick.  Source/audit Git-blob SHA-256 are
`2f70d3506436590e77654c9e08670f32d66965d0bc413033bc2c9223e0138329`
and
`74f5dc0d70bc3fac6f0297aaf032b32310809b87641f5bfa055d355c4212de2b`.
Runner v1 checkpoint `56a637877bcc02cedafe00b5910a08243caaa792`,
Git-blob SHA-256
`51c7202f1469fa62a17cf806ac83df650f691fed934a177b76335c9bbed18244`,
pins that source and places a finite-sum/sign repro before the focal.
Notebook checkpoint `f795fb52f7196bbd26c3f843ed08419d19623647`, Git-blob
SHA-256
`c84aee6ec0ff84a0d7fd339412d3a1e89ab50860866fe668775a737d4508adf8`,
pins the runner.  The queued result remains NOT CHECKED.

Diagnostic v1 ran once in a fresh Colab Pro+ CPU/high-RAM clone under the
visible account `lluiseriksson@gmail.com` at exact source
`34f75aa60e39301a7fd281054513bfce5fe99cc2`.  Runner transport, exact
source/blob hashes, official Lean/Mathlib pins, both text guards and the
Mathlib-only repro passed.  The focal stopped with exit code `1` after
`2481.662 s`; stop-on-first-error prevented the audit.  The only goal exposed
the definitionally identical signed-alias equivalence once as the local
abbreviation `e` and once literally; the proof had not unfolded `e` in that
reindexing step.  Evidence/archive SHA-256 are
`56dcc6b572b9930fc59fe3c2ac3844af91c302f0b62e488dd6d24cdc1c7d0c9f`
and
`4dee3db7339cf0058e3a3aba24d02400ae4807ce5e7dbf0cbc5db427ff9c5d9e`.
`FINAL_STATUS=FAIL`; the runtime released automatically and the cell was not
rerun.  The v2 repair unfolds only that local abbreviation; statements,
hypotheses, constants and scope remain unchanged.  PRE-VALIDATION remains
visible and v2 is NOT CHECKED.  Repair checkpoint
`cfb67cb9cab17889d3416358f981a336815a4ef8` has source Git-blob
SHA-256
`5c92cc36c1eb2544ded179b9c0b93145b725fcbe818d1f6200e7ecc9e974ead8`.
Runner v2 checkpoint `c8d02d5cc42cd3198b064340b4e76c210f7dae48`, Git-blob
SHA-256
`7a781c442bc59cdf7019f0eb26e7b6ea9c021da9e6f114dad9ec41e19cf423df`,
adds the exact local-abbreviation repro.  Notebook checkpoint
`b50417d466972b2a4fdb3e54f37b82d35a11a523`, Git-blob SHA-256
`ba4e29e9c01069581f6cd1a9f330d6548821b3c4d6e400abfba668872d9e3a65`,
pins v2.

Diagnostic v2 passed once in a fresh Colab Pro+ CPU/high-RAM clone at exact
source `cfb67cb9cab17889d3416358f981a336815a4ef8`.  All runner transport,
source/blob, official Lean/Mathlib pin, exact text-guard and repro gates
passed.  The focal returned exit code `0` after `1576.064 s`, with literal
terminal line `Build completed successfully (8702 jobs).`; the audit returned
exit code `0` after `7.176 s`, and all five declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence/archive SHA-256 are
`42a1c30b5bb7d0bf405b82cc485353fa36a01d95d7ecd8dbdc31e4b234742f50`
and
`b329e9993815eca5836f73ef78d7c091dec48858c78b50ce2bf0b7b7ac9be837`.
`FINAL_STATUS=PASS`; the runtime released automatically and the cell was not
rerun.  The seal retires exactly the source and audit PRE-VALIDATION marks.
It covers the zero-coarse-fibre endpoint reflection and complete finite alias
sum only.  A combined zero/nonzero consumer, Brillouin integration, regional
`B0`, window-15 attainment and terminal fields remain open.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

### Step 8b.21: complete physical-fibre endpoint integrand (SEALED)

`BalabanCMP99SourceFlatQprimeCompleteEndpointIntegrand` first reindexes the
column-oriented physical fibre through the literal signed-alias equivalence
and identifies the complete sum with the CMP89 stabilized endpoint
integrand.  Its second theorem splits only on the actual coarse mode: nonzero
fibres consume the sealed Fourier-negation quotient transport, while the
singular zero fibre consumes the sealed Eq. (249) reflection.  Both branches
land at one literal endpoint-integrand target; no `if` wrapper or termwise
identification of the affine carry with reflection is introduced.

No Lean, Lake or oracle ran for this brick on Windows.  Brillouin integration,
regional `B0`, window-15 attainment, terminal fields and a `TermSource`
inhabitant remain open.
Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.

Source checkpoint `063f4337faba31ce7e5235e8c915a24b602a33a6` has
source/audit Git-blob SHA-256
`4437f382c9a19951141ff2503a69beabf41603be59751c35d79a789ffbe4bb45`
and
`144f1b3814bfe62e0e252e89169194f534f4fbf25b6e794f8c02301d9ad88b13`.
Runner v1 checkpoint `7c24b5be3d6587990b08be6acfe977251871403a`,
Git-blob SHA-256
`071b7adac47133c39040eaee44a3de7b5088abdbbc1d25aee7f9306074d327d3`,
places exact equivalence-reindexing and case-split repros before the focal.
Notebook checkpoint `eab84571d72cd5b5b938f405ce186201e0b9ebd9`, Git-blob
SHA-256
`93036ee8349eb2712740f3cb312c966b773450893c660b46e218e73051cb4b3d`,
pins the runner.

One fresh Colab CPU/high-RAM clone at exact source
`063f4337faba31ce7e5235e8c915a24b602a33a6` passed every transport, blob,
pin, text and repro gate.  The focal exited `0` after `1727.387 s` with the
literal terminal line `Build completed successfully (8703 jobs).`; the audit
exited `0` after `8.152 s`, and both declarations printed exactly
`[propext, Classical.choice, Quot.sound]`.  Evidence SHA-256 is
`1195ba89172c8e065b386f38a45ef224f53ec99225734887289e3e5ccd487330`;
archive SHA-256 is
`7806b769510a0b7c2f73a53e8ea5ba9f60348c58ea8897ad43919d2ed562d553`.
`FINAL_STATUS=PASS`; the runtime auto-unassigned and no rerun occurred.  This
seal retires exactly the two Step-8b.21 PRE-VALIDATION marks.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.

### Step 8b.22: exact finite-grid Fourier aliasing substrate (SEALED; cold run 31991954503; 20/41 unchanged)

`BalabanCMP99FlatFiniteGridAliasing` starts item 3 of the finite post-Gate-7
route without identifying a finite DFT with an integral.  It reduces integer
Fourier frequencies into the exact multidimensional `ZMod` box, proves the
normalized character selector for an arbitrary residue class, and uses
absolute summability to exchange the finite grid sum with the infinite
Fourier series.  The endpoint is the literal sum of continuous coefficients
in that residue class.

Cold GitHub Actions run [31991954503](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31991954503), job `95276977132`, validated exact
source `534493728038813f3772f8b3b073237f4da1884e` under workflow HEAD `b05ef65af97a95752d1c929e30749d886d425d8d`.
The focal exited `0` after `1277 s` with literal
`Build completed successfully (8478 jobs).`; the audit
exited `0` after `7 s`.  All seven measured
axiom blocks are recorded in ledger Addendum 867 and are subsets of
`{propext, Classical.choice, Quot.sound}`.  `FINAL_STATUS=PASS` and the
independent artifact audit verified `13` manifest
entries, `14` inner members and
`16` outer members.

The physical Fourier-series expansion of the CMP89 endpoint integrand is not
accepted as a premise or asserted here; it remains the next source-specific
producer.  This seal covers generic finite-grid aliasing only.  Regional
`B0`, window 15, terminal fields and a `TermSource` inhabitant remain open.
Counters stay exactly `20/41`, `TermSource = 0`; window 15 remains compatible
but unattained.

### Step 8b.24/C6c.2 P0 canonical retained-prefix tower (SEALED; P1 next)

Fresh Colab Pro+ validation of source
`033469bb1a816de9979ac04867779e2fb7a196cd` compiled the promoted public
`BalabanCMP99SourceCanonicalPrefixTower` module and its ten-readout sibling
audit.  The focal exited `0` after `922.615 s` with `8465` jobs and the audit
exited `0` after `13.583 s`; every readout used exactly
`{propext, Classical.choice, Quot.sound}`.  Independent transcript validation
is recorded in ledger Addendum 868.

This is the first sealed public brick of the sequential P0--P9 prefix-Green
chain.  It fixes the canonical retained-prefix truncations and their tower
transport; P1 coefficient monotonicity remains the immediate successor and
may not be bypassed.  P0 does not produce the CMP96 Dirichlet defect, a
uniform CMP99 (3.42) pair, the four regional actions, window 15, a terminal
field, or a `TermSource`.  The live count remains exactly `20/41` and
`TermSource = 0`; window 15 remains compatible but unattained.

### Step 8b.24/C6c.2 P0--P9 promoted prefix-Green graph (SEALED; fresh Colab Pro+ clone; 20/41 unchanged)

One fresh Colab Pro+ CPU/high-RAM clone compiled and audited the full public
P0--P9 graph at exact source
`10e6899692defec09b416d73a64ec36ee5cc7393`.  Both cold prerequisite
materializations and all 39 numbered focal/audit stages exited `0`.  The 20
audits emitted exactly 200 axiom headers; every set is a subset of
`{propext, Classical.choice, Quot.sound}`, with neither `sorryAx` nor
`ofReduceBool`.  The evidence-payload SHA-256 is
`49F216701E4B0BEB22BF4FB8442F2699FF471B2170111ED9BF095E4064418562`;
the downloaded archive SHA-256 is
`45443DB78A7FE08AD956462EEA6E992D2737F41B18940BF4F9C8E643A476A782`.
The archive was verified locally before the runtime was disconnected and
deleted; the cell was not rerun.

The seal fixes the canonical prefix recursion, base and coarse covariances,
the Eq. (2.34) finite scale sum, the source-separated ambient precision, the
canonical regional Green and the per-depth Combes--Thomas bounds.  It does
**not** produce a uniform CMP99 (3.42) pair, any of the four source-localized
actions, the C6c.4 supremum, window-15 attainment, a terminal field or a
`TermSource` inhabitant.  In particular, the per-depth bound
`2 / coercivity` is not relabelled as the source-uniform `B0`.  Counters stay
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.


### Step 8b.23: source-specific physical Green Fourier route, Units A--E (SEALED; cold checkout; 20/41 unchanged)

The eighteen ordered bricks from the centered Brillouin/torus dictionary
through the literal physical finite-grid aliasing endpoint have been compiled
and audited together.  The route constructs the common mass-uniform strip,
the signed product-contour displacement, normalized Green bounds, the exact
torus coefficient dictionary, absolute Fourier summability and the
source-specific Step-8b.22 consumer.  No free Fourier-series identity is
accepted at the endpoint.

One cold GitHub Actions checkout validated exact source `9d378412d4fa282dc92728154e93d58bd9843bfe` in
terminal run `32329127991` (https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/32329127991).  All 36 focal/audit stages exited `0` in
1617 aggregate stage-seconds.  The 18 audits emitted exactly
124 axiom blocks, each a subset of
`{propext, Classical.choice, Quot.sound}`; the artifact contains literal
`FINAL_STATUS=PASS`.  Inner archive SHA-256 is
`90D66229E393768C17B2698012AD78A98DF358DF3B4BA2D49EF5F18DCA8C7DB9` and raw outer artifact ZIP SHA-256 is
`1E5002004D4789D1F00F0CA0D2A87642752056EDBD07FF948C89EFE8D79C3F38`.

This is a source-specific A--E seal, not Unit F and not regional `B0`.
Window 15 is still compatible but unattained; no terminal field is discharged
and no `TermSource` inhabitant is constructed.  Counters remain exactly
`20/41`, `TermSource = 0`.


### Step 8b.23 Unit F: post-aliasing periodic owner decay (SEALED; cold checkout; 20/41 unchanged)

The four Unit-F bricks from the centered periodic residue sum through the
diagonal finite Green owner bound have been compiled and audited together.
The route retains exponential decay in the centered periodic representative
without a volume factor and installs the exact endpoint and zero-residue
dictionaries used by the diagonal Gate-7 carrier.

One cold GitHub Actions checkout validated exact source `fa29c350fd216305b56685b15a6aee3d80e46ae7` in
terminal run `32343215395` (https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/32343215395).  All eight focal/audit stages exited `0`
in 1168 aggregate stage-seconds.  The four audits emitted exactly 49
axiom blocks, each a subset of `{propext, Classical.choice, Quot.sound}`;
the artifact contains literal `FINAL_STATUS=PASS`.  Inner archive SHA-256 is
`3412526E138F4ED891F8A87303A293E7776F07EC065D047A9CD0BF7BE9128D12` and raw outer artifact ZIP SHA-256 is
`187014EEBDB5DE37ADE100696E040E46B42EE535325D4493A5331EBC76A06035`.

This is the Unit-F periodic-owner seal only, not the independent-scale
regional `B0` dictionary and not window-15 attainment.  No terminal field is
discharged and no `TermSource` inhabitant is constructed.  Counters remain
exactly `20/41`, `TermSource = 0`.


### Step 8b.24/C4a: literal endpoint to Unit-F owner dictionary (SEALED; fresh Colab Pro+ clone; 20/41 unchanged)

The source-separated endpoint uses the literal integer displacement
`x - M*y`, whereas Unit F consumes the shortest periodic displacement from
`x` to the canonical fine-block basepoint of `y`.  These signed vectors need
not agree at an even antipodal seam.  C4a proves the exact invariant that is
actually consumed: equality of their centered `l1` lengths, hence equality of
their signed-lattice exponential weights, and transports the sealed Unit-F
owner estimate without asserting a false signed-vector identity.

One fresh Colab Pro+ CPU/high-RAM clone compiled exact source checkpoint
`cb92d619c8ff95781d1f51ec9fad823b996120b4` using instrumental runner
`bbd83565af5be389c997889bbea36e162bf2c68c`.  The exact Lean 4.29.0-rc6 asset,
Mathlib pin `07642720480157414db592fa85b626dafb71355b`, nine manifest package
pins and both source-blob hashes passed before compilation.  The focal built
successfully in `2230.551 s` with `8649` jobs; the audit exited `0` in
`9.967 s`.  Its four axiom blocks are respectively
`{propext, Quot.sound}` and three copies of
`{propext, Classical.choice, Quot.sound}`.  Canonical evidence SHA-256 is
`41F32D4F88608D1EA3D6E95CCF31201C34FB2C17DA653ECFEF1545D1AB33B24C`;
archive SHA-256 is
`777AFEC8287F9DDB20927F268693A11739F04551DD1281FE36858480124DDF29`.
The runner emitted literal `FINAL_STATUS=PASS` and auto-disconnected the
runtime.

This seal is the literal endpoint-to-owner dictionary consumed by C4b.  It is
not regional `B0`, does not attain window 15, does not discharge a terminal
field and does not construct a `TermSource` inhabitant.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.


### Step 8b.24/C4b: generated point-source Green to Unit-F owner bound (SEALED; fresh Colab Pro+ clone; 20/41 unchanged)

One fresh Colab Pro+ CPU/high-RAM clone compiled exact source checkpoint
`7c0c25a3c1468bfbec0fb64340b31d03264d185f` using instrumental runner
`5cc5ea8c2467f7e60d263233a642449a3860693d` (revision
`source-point-owner-v7-zero-weight-normalization`).  The exact Lean
4.29.0-rc6 asset, Mathlib pin
`07642720480157414db592fa85b626dafb71355b`, all manifest package pins and
all 26 source-blob hashes passed before compilation.  The focal built
successfully in `2465.188 s` with `8751` jobs.  All thirteen audit stages
exited `0`.

The audits emitted 39 axiom blocks.  Two are the constructive subset
`{propext, Quot.sound}` and the remaining 37 are
`{propext, Classical.choice, Quot.sound}`; neither `sorryAx` nor
`ofReduceBool` occurred.  Canonical evidence SHA-256 is
`D7A022D379791C907F6A59A0090C5CAE2F848DFD209389ECF262DD32CDC865F1`;
archive SHA-256 is
`05A2EEBF44653C233C13F41FC10289B565FDF5B4BFC5E807D1D00F1E273D5FB0`.
The runner emitted literal `FINAL_STATUS=PASS`, requested unassignment and
the runtime was confirmed disconnected.

The sealed route internally constructs the complex point-source Fourier
reconstruction, neutral mass-zero noncentral symbol, source-separated
ambient Green and complexification, exact Step-7b carrier and precision
dictionary, physical Fourier endpoint, literal endpoint integrand,
zero-residue aliasing and the final Unit-F owner estimate.  It is the C4b
point-source chain, not a uniform regional `B0` producer, not attainment of
window 15, not a terminal field and not a `TermSource` inhabitant.  Counters
remain exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.


### Step 8b.24/C5: source-localization owner transport (SEALED; 20/41 unchanged)

Source checkpoint `d8b873a4abf6d83bdf57068ff850a90335974f40`
promotes the source/audit pair for C5.  The theorem evaluates the sealed C4b point-source bound at the exact
`cmp99Eq389SourceLocalizationSiteEquiv` and rewrites the fine-block owner to
the literal `cmp99Eq389SourceLocalizationOwner`.  No free readout,
cardinality equivalence or diagonal `K=L` identification is introduced.

One fresh Colab Pro+ CPU/high-RAM clone validated the exact source checkpoint
with runner revision `source-owner-transport-v1`.  The focal completed 8752
jobs in `1610.217 s`; the one-declaration audit completed in `11.002 s` and
printed exactly `{propext, Classical.choice, Quot.sound}`.  Canonical evidence
SHA-256 is `72CEC2F1C5CFDA1196745ABFE991D6346E7FF30DE85FDBE8E2AEA7AD3F423738`;
archive SHA-256 is `E8C3E56A84736058671B47D32CA4C4B45EB660641A4C8065D94E0FDE8E25E209`.
The runner emitted literal `FINAL_STATUS=PASS`, requested unassignment and the
runtime was confirmed disconnected.

The seal retires exactly the two C5 PRE-VALIDATION marks and imports its audit
into `YangMillsCore.lean`.  This is source-owner transport only,
not a point-source `B0`, not a uniform regional `B0`, not attainment of
window 15, not a terminal field and not a `TermSource` inhabitant.  Counters
remain exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.


### Step 8b.24/C6a: named ambient point-source `B0` (SEALED; 20/41 unchanged)

PRE-VALIDATION source checkpoint
`1abd6761599da1ab9ade88601e4fc7f96b47a8b5` promotes the C6a source/audit
pair.  It names the complete coefficient already displayed by sealed C5,
proves its nonnegativity on the same physical strip window, and restates the
point-source estimate in that exact named-coefficient form.

The coefficient remains explicitly depth-dependent through the generated
physical `a`.  C6a is therefore an ambient point-source coefficient, not a
uniform regional `B0`, not attainment of window 15, not a terminal field and
not a `TermSource` inhabitant.

Fresh Colab diagnostic v1 stopped at the first focal error after `1679.035 s`:
the nonnegativity proof had not unfolded the signed-lattice exponential weight
at displacement zero, so simplification left the true extra factor visible.
Evidence SHA-256 is
`8284C182511357E6B12795555E53E24D58A7C83E6225E1125C3C0B1469FFBD8F`;
archive SHA-256 is
`C1600E358C42ADD06F4C17D222F9A78A7A4BA58596C141C2861BEA4A37DCCFE7`.
This is a measured elaboration failure only.  PRE-VALIDATION remains and no
counter moves; v2 unfolds the two already sealed weight definitions at zero
without changing the statement, coefficient, hypotheses or scope.  Repair
checkpoint `1f53807c6040a0856ca98e49f610d40d6b28fed7` remains visibly
PRE-VALIDATION pending that v2 diagnostic.

Fresh Colab diagnostic v2 checked exact repair checkpoint
`1f53807c6040a0856ca98e49f610d40d6b28fed7` with runner revision
`point-source-b0-v2-zero-weight-normalization`.  The focal completed `8753`
jobs in `1761.617 s`; the three-declaration audit completed in `14.647 s` and
each declaration printed exactly `{propext, Classical.choice, Quot.sound}`.
Canonical evidence SHA-256 is
`680BBABE748F9A1807088B38CC329C195B550E9D768AC2C777CE55DEFB2D149C`;
archive SHA-256 is
`B38478583070BC5CD6B08BC62C215F81DC721EE7FCB7223C8BC60C768FB8E6A0`.
The runner emitted literal `FINAL_STATUS=PASS`, requested unassignment and the
runtime was closed.

This seal retires exactly the two C6a PRE-VALIDATION marks and imports its
audit into `YangMillsCore.lean`.  It certifies the named ambient point-source
coefficient and its nonnegativity, not uniform regional `B0`, window-15
attainment, a terminal field or a `TermSource` inhabitant.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but unattained.


### Step 8b.24/C6b: identity-owner localized coarse-field `B0` (SEALED; 20/41 unchanged)

PRE-VALIDATION source checkpoint
`8839c2378cec95793663b204661ed9b32c367dfd` promotes the C6b source/audit
pair.  It proves that a coarse field supported in one fibre of the literal
identity owner map is definitionally the corresponding point source, then
feeds that equality into sealed C6a and bounds the source value by the
existing finite supremum norm.  No source-cardinality factor is introduced.

One fresh Colab Pro+ CPU/high-RAM clone checked the exact source checkpoint
with instrumental checkpoint `1572f8f3cbf915ce3e858efbcdc845c63c700c1b`,
runner revision `localized-field-b0-v1`, and runner SHA-256
`7039EE3CC0C22C3A6C10D7C59A3A9880EF22DC991D6FA7BC271CC35C66160E4A`.
The focal completed `8754` jobs in `1777.368 s`; the two-declaration audit
completed in `11.669 s`, and both declarations printed exactly
`{propext, Classical.choice, Quot.sound}`.  Canonical evidence SHA-256 is
`3B131C83835688A8DA2CCFCDA3E149E4C7B0FD2935101104D67271255A167750`;
archive SHA-256 is
`9AA016F3AA23567E182CE4197AAD38058CCE66712B84EB29C7DD01277583A29C`.
The runner emitted literal `FINAL_STATUS=PASS`, requested unassignment and
the runtime was closed.

This seal retires exactly the two C6b PRE-VALIDATION marks and imports its
audit into `YangMillsCore.lean`.  The conclusion still concerns the ambient
complex operator `G Q'^*` and the C6a coefficient remains explicitly
depth-dependent.  C6b is therefore not the canonical real regional Dirichlet
Green, not the uniform regional (3.42) certificate, not attainment of window
15, not a terminal field and not a `TermSource` inhabitant.  Counters remain
exactly `20/41`, `TermSource = 0`; window 15 remains compatible but
unattained.


### Step 8b.24/C6c.3: signed cutoff-Laplacian species (SEALED; fresh Colab Pro+ clone; 20/41 unchanged)

Source checkpoint `abf69f4410c570c39525ccfd5a0a6a72c1caabbe` was validated
from instrumental checkpoint `0565c88b098faaf1f7ec0028bd3c4ea807b14eec` in a fresh
Colab Pro+ CPU/high-RAM clone.  Runner revision `c6c3-signed-cutoff-v1`,
SHA-256
`F3AC422B63CAA1535327E56F92840329A867E09B465FB1091E35F5F01E8E4B17`,
verified the source chain, both Git blobs, toolchain and manifest before
compilation.  The focal completed `8525` jobs in `1970.820 s`; the
four-declaration audit completed in `13.210 s`, and every declaration printed
exactly `{propext, Classical.choice, Quot.sound}`.  Canonical evidence
SHA-256 is
`EED96C0286A8F42D060B599043A7B5E1D37D44D7CC011707AC48173DEFBD9BB6`;
archive SHA-256 is
`D2D8A5FE2CD37C59F91B4822B01603B0D7583179FE877ACDDB6DE76A0BAEF4F2`.
The transcript contains literal `FINAL_STATUS=PASS`; unassignment was
requested and the runtime was closed.

The seal certifies the literal middle species inside `K(h)` with the source
minus sign, its equality with the negative of the positive cutoff correction
in the tree's `D^*D` product rule, the pointwise
`48 * secondDerivBound / cutoffScale^2` estimate and the exact range-squared
normalization `12 * secondDerivBound / K^2`.  It constructs no Green, cell or
layer sum, local defect, contraction, window-15 attainment, terminal field or
`TermSource`.  Counters remain exactly `20/41`, `TermSource = 0`; window 15
remains compatible but unattained.


### Step 8b.24/C6c.4a: arbitrary-input tilted inverse action (SEALED; fresh Colab Pro+ clone; 20/41 unchanged)

Source checkpoint `dab2c355e0b6e73f9c95fa5d4a8124bbf935e611` was validated
from instrumental checkpoint `b56754ee4c02f5c54738da28a54952fe78999635` in one fresh
Colab Pro+ CPU/high-RAM clone.  Runner revision `tilted-inverse-action-v1`,
SHA-256
`E9E0C0699FAAE40EDB9376FB5A1B2D42095935483752B86683ED222827DB02BF`,
verified the source chain, both Git blobs, toolchain and manifest before
compilation.  The focal completed `8171` jobs in `86.769 s`; the
one-declaration audit completed in `5.315 s` and printed exactly
`{propext, Classical.choice, Quot.sound}`.  Canonical evidence SHA-256 is
`0848F2388FC27DB4ED163C4A331990F5B40BCFA53D193DB75F858E17D3A06689`;
archive SHA-256 is
`B694A49B17AAF9423CB8AA3DA16D428E908402EC5C00FF71FB980AB9606D81AA`.
The transcript contains literal `FINAL_STATUS=PASS`; unassignment was
requested and the runtime was closed.

The theorem preserves an arbitrary input and concludes with exactly
`‖tilt f‖₂`; it never expands the source into coordinate probes and introduces
no fine-fibre cardinality.  Source-owner support, the one permitted `ell²`
conversion, fine-to-owner distance, uniform physical `B0`/`delta0`, the
canonical regional specialization, window 15, terminal fields and
`TermSource` remain open.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.
