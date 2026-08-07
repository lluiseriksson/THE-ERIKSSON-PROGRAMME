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
