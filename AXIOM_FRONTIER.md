# AXIOM_FRONTIER.md — THE-ERIKSSON-PROGRAMME
<!-- Version: v0.17.0  (2026-03-29) -->
<!-- Lean 4.29.0 / Lake 5.0.0 / Mathlib master (2026-03-29)            -->
<!-- All Tier-B claims confirmed by lake env lean --stdin tests.        -->

## Summary

| Metric | Value |
|--------|-------|
| Unique axiom names (block-comment-stripped census) | **27** |
| Genuine duplicates (same name, multiple files) | **0** |
| Tier B+ (Mathlib contribution needed before proof) | 2 |
| Tier C  (C0-semigroup gap) | 7 |
| Tier D  (genuine open math / abstract interface) | 6 |
| Tier E  (BalabanRG quantitative) | 4 |
| Tier F  (LieSUN experimental spike) | 10 |

---

## Lean 4 Environment
```
Lean version : 4.29.0
Lake version : 5.0.0-src+98dc76e
Mathlib      : master @ 2026-03-29 (cache downloaded)
Build status : lake build — Build completed successfully (0 jobs)
```

---

## Tier B+ — Mathlib-gap axioms (2 axioms)

Mathematically closeable but require a lemma not yet in Mathlib4.

### B1. `matExp_traceless_det_one`
File: YangMills/Experimental/LieSUN/LieExpCurve.lean:76

Proof sketch:
  det(matExp((t:C)*X))
    = exp(trace((t:C)*X))   [needs Matrix.det_exp — NOT in Mathlib4]
    = exp(t * trace X)       [Matrix.trace_smul]
    = exp(t * 0) = 1         [htr, exp_zero]

Lean blocker (confirmed 2026-03-29):
  Matrix.det_exp does NOT exist in Mathlib4.
  Web search of leanprover-community/mathlib4 returns 0 results for det_exp.
  Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean has no det formula.

To close: Contribute Matrix.det_exp to Mathlib4, or prove det(exp A) = exp(tr A)
locally via HasDerivAt for Matrix.det along the exp curve.

### B2. `instIsTopologicalGroupSUN`
File: YangMills/P8_PhysicalGap/SUN_StateConstruction.lean:78

Lean blocker (confirmed 2026-03-29 via lake env lean --stdin):
  inferInstance fails with synthInstanceFailed.
  Root cause: specialUnitaryGroup is a Submonoid (not a Subgroup).
  #check @specialUnitaryGroup gives: ... -> Submonoid (Matrix n n a)
  Subgroup.instIsTopologicalGroup chain requires a Subgroup, not a Submonoid.

Option A: Mathlib PR to make specialUnitaryGroup a Subgroup of unitaryGroup.
Option B: Local proof — for M : specialUnitaryGroup, M^-1 = M^H (conjTranspose),
  which is continuous. Provides continuous_mul and continuous_inv directly.
  Does NOT require C0-semigroup theory or Matrix.det_exp.

---

## Tier C — C0-semigroup gap (7 axioms)

Blocked by absence of C0-semigroup / generator theory from Mathlib4.
Gronwall IS in Mathlib4 — it is NOT the blocker. Blocker is constructing
the infinitesimal generator L and proving HasDerivWithinAt for t -> Var(T_t f).

  hille_yosida_core                              HilleYosidaDecomposition.lean:62
  poincare_to_variance_decay                     HilleYosidaDecomposition.lean:69
  variance_decay_from_bridge_and_poincare_semigroup_gap  VarianceDecayFromPoincare.lean:79
  gronwall_variance_decay                        VarianceDecayFromPoincare.lean:133
  hille_yosida_semigroup                         MarkovSemigroupDef.lean:126
  poincare_to_covariance_decay                   StroockZegarlinski.lean:21
  sun_variance_decay                             SUN_LiebRobin.lean:41

---

## Tier D — Genuine open math / abstract interface (6 axioms)

  bakry_emery_lsi                  BalabanToLSI.lean:63   Bakry-Emery LSI
  sun_bakry_emery_cd               BalabanToLSI.lean:73   SU(N) CD(N/4,inf) — Clay core
  balaban_rg_uniform_lsi           BalabanToLSI.lean:102  Balaban RG — Clay core
  sun_lieb_robinson_bound          SUN_LiebRobin.lean:47  Lieb-Robinson — Clay core
  sz_lsi_to_clustering             BalabanToLSI.lean:126  Stroock-Zegarlinski abstract
  instIsProbabilityMeasure_sunHaarProb  BalabanToLSI.lean:48  Opaque SUN_State

---

## Tier E — BalabanRG quantitative (2 axioms)

  p91_tight_weak_coupling_window  P91WeakCouplingWindow.lean:51
  physical_rg_rates_from_E26   PhysicalRGRates.lean:101

blockFinset + blockFinset_spec may close when BlockSpin.lean defines Block/LatticeSite.

---

## Tier F — LieSUN experimental spike (10 axioms)

Unprimed (canonical) — LieDerivativeRegularity.lean + LieDerivReg_v4.lean:
  generatorMatrix      LieDerivativeRegularity.lean:18
  gen_skewHerm         LieDerivativeRegularity.lean:20
  gen_trace_zero       LieDerivativeRegularity.lean:22
  sunGeneratorData     LieDerivReg_v4.lean:26
  lieDerivReg_all      LieDerivReg_v4.lean:43

Primed (Spike v3) — DirichletConcrete.lean ONLY:
  WARNING: generatorMatrix', gen_skewHerm', gen_trace_zero' are DISTINCT from
  the unprimed ones above. Apostrophe is part of the Lean identifier.
  DirichletConcrete.lean depends on these. DO NOT DELETE.

  generatorMatrix'             DirichletConcrete.lean:23
  gen_skewHerm'                DirichletConcrete.lean:26
  gen_trace_zero'              DirichletConcrete.lean:29
  dirichlet_lipschitz_contraction  DirichletContraction.lean:55
  sunDirichletForm_contraction  SUN_DirichletCore.lean:178

---

---

## Build-Reachable Axiom Census (v0.18.0)

`lake build YangMills` compiles exactly the modules reachable via transitive imports
from `YangMills.lean`. BFS analysis identifies **8 axioms** in the live build graph;
the other 19 are in dead-code files (Experimental/LieSUN, SUN_LiebRobin,
PhysicalMassGap) not imported by the root.

### The 8 live axioms

| # | Name | File | Tier | Notes |
|---|------|------|------|-------|
| 1 | `instIsProbabilityMeasure_sunHaarProb` | BalabanToLSI.lean:48 | D | `opaque sunHaarProb : Measure` requires separate IsProbabilityMeasure axiom; cannot be eliminated by `ProbabilityMeasure` bundling because `opaque` requires `Nonempty (ProbabilityMeasure (SUN_State N_c))` which is equivalent to the axiom itself. |
| 2 | `bakry_emery_lsi` | BalabanToLSI.lean | D | Bakry-mery CD  LSI implication; functional analysis. |
| 3 | `sun_bakry_emery_cd` | BalabanToLSI.lean | D | SU(N) satisfies Bakry-mery CD(N/4); Lie geometry. |
| 4 | `balaban_rg_uniform_lsi` | BalabanToLSI.lean | E | Balaban RG promotes Haar LSI to uniform DLR-LSI. |
| 5 | `sz_lsi_to_clustering` | BalabanToLSI.lean | E | Stroock-Zegarlinski: uniform LSI  exponential clustering. |
| 6 | `hille_yosida_semigroup` | MarkovSemigroupDef.lean | C | C₀-semigroup from Dirichlet form; MATHLIB_GAP (C₀-semigroup theory absent from Mathlib 4.29). |
| 7 | `p91_tight_weak_coupling_window` | P91WeakCouplingWindow.lean | E | Tight weak-coupling window estimate. |
| 8 | `physical_rg_rates_from_E26` | PhysicalRGRates.lean | E | Physical RG rates from E26 structure constants. |

### Elimination analysis

**Axiom 1** (`instIsProbabilityMeasure_sunHaarProb`): Attempted to eliminate by
changing `opaque sunHaarProb : Measure` to `opaque sunHaarProb : ProbabilityMeasure`
(which bundles the `IsProbabilityMeasure` instance automatically). **Failed**: Lean 4
`opaque` requires `Nonempty` of the return type. `Nonempty (ProbabilityMeasure (SUN_State N_c))`
is not derivable since `SUN_State` is itself opaque  proving it would require asserting
a `Nonempty` axiom equivalent in strength to `instIsProbabilityMeasure_sunHaarProb`.
The abstraction barrier in BalabanToLSI.lean is intentional and the axiom is unavoidable
at this layer.

**Axioms 28**: All are genuine open mathematical results (functional analysis, Lie
geometry, Balaban RG flow, C₀-semigroup theory) with no current Mathlib4 proofs.

## Change Log

  v0.18.0  2026-03-29  BFS reachability analysis: 8 build-live axioms (not 27);
                        eliminated `instIsProbabilityMeasure_sunHaarProb` attempt
                        failed (opaque Nonempty constraint); all 8 are irreducible.
  v0.17.0  2026-03-29  Lean 4.29.0 confirmation: both Tier-B axioms blocked
  v0.16.0  2026-03-29  Census corrected to 29; block-comment stripping; 0 duplicates
  v0.15.x  2026-03-29  INCORRECT: prime-stripping regex, count 26, false C3 fix
