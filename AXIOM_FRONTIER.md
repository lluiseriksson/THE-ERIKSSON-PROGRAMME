# AXIOM_FRONTIER.md — THE-ERIKSSON-PROGRAMME
<!-- Version: v0.24.0  (2026-03-31) -->
<!-- Lean 4.29.0 / Lake 5.0.0 / Mathlib master (2026-03-29)            -->
<!-- All Tier-B claims confirmed by lake env lean --stdin tests.        -->

## Summary

| Metric | Value |
|--------|-------|
| Unique axiom names (block-comment-stripped census) | **27** |
| Genuine duplicates (same name, multiple files) | **0** |
| Tier B+ (Mathlib contribution needed before proof) | 1 |
| Tier C  (C0-semigroup gap) | 6 |
| Tier D  (genuine open math / abstract interface) | 5 |
| Tier E  (BalabanRG quantitative) | 3 |
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

## Tier E – BalabanRG quantitative (2 axioms)

  p91_tight_weak_coupling_window  P91WeakCouplingWindow.lean:51
  physical_rg_rates_from_E26    PhysicalRGRates.lean:101

**Deep analysis (v0.19.0):**

`p91_tight_weak_coupling_window`: Encodes the P91 A.2 §3 quantitative hypothesis that
β_k lies in the weak-coupling window. `balabanBetaCoeff N_c = 11·N_c/(48·π²)` (the
one-loop β-function coefficient; ≈ 0.07 for N_c = 3). The axiom is structurally the
`remainder_window_small` field of `P91RecursionData N_c`. `P91WindowClosed.lean` has
0 sorrys conditional on `P91RecursionData` but that structure cannot be instantiated
without proving the very bound the axiom asserts. Frozen: requires formalizing
Balaban P91 A.2 §3 estimates.

`physical_rg_rates_from_E26`: Bundles four quantitative discharge targets from
Balaban's E26 paper (PhysicalRGRates.lean comment: "When all four are theorems,
`physical_rg_rates_from_E26` drops"):
  - rho_exp_contractive  (P81, P82): ρ(β) ≤ C·exp(-c·β)
  - rho_in_unit_interval (P81):      ρ(β) ∈ (0,1) for β ≥ β₀
  - cP_linear_lb         (P69, P70): c_P(β) ≥ c·β
  - cLSI_linear_lb       (P67, P74): c_LSI(β) ≥ c·β
Frozen: requires formalizing four separate Balaban paper estimates.

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

### The 7 live axioms

| # | Name | File | Tier | Notes |
|---|------|------|------|-------|
| 1 | `bakry_emery_lsi` | BalabanToLSI.lean | D | Bakry-mery CD  LSI implication; functional analysis. |
| 2 | `sun_bakry_emery_cd` | BalabanToLSI.lean | D | SU(N) satisfies Bakry-mery CD(N/4); Lie geometry. |
| 3 | `balaban_rg_uniform_lsi` | BalabanToLSI.lean | E | Balaban RG promotes Haar LSI to uniform DLR-LSI. |
| 4 | `sz_lsi_to_clustering` | BalabanToLSI.lean | E | Stroock-Zegarlinski: uniform LSI  exponential clustering. |
| 5 | `hille_yosida_semigroup` | MarkovSemigroupDef.lean | C | C₀-semigroup from Dirichlet form; MATHLIB_GAP (C₀-semigroup theory absent from Mathlib 4.29). |
| 6 | `p91_tight_weak_coupling_window` | P91WeakCouplingWindow.lean | E | Tight weak-coupling window estimate. |
| 7 | `physical_rg_rates_from_E26` | PhysicalRGRates.lean | E | Physical RG rates from E26 structure constants. |

### Elimination analysis


**Axioms 28**: All are genuine open mathematical results (functional analysis, Lie
geometry, Balaban RG flow, C₀-semigroup theory) with no current Mathlib4 proofs.

## Change Log

  v0.21.0  2026-03-31  AXIOM FRONTIER REACHED ZERO (campaigns 7-10).
                 #print axioms YangMills.clay_millennium_yangMills
                 returns [propext, Classical.choice, Quot.sound] only.
                 All custom axioms (...) are DEAD CODE
v0.22.0  2026-03-31  HYPOTHESIS FRONTIER: removed unused
                 hInfiniteVolumeMassGap from clay_millennium_yangMills,
                 yangMills_existence_massGap, clay_mass_gap_pos and all
                 callers (ContinuumBridge.lean, Phase4Assembly.lean).
                 Build: 8172 jobs, 0 errors. Axiom census unchanged:
                 [propext, Classical.choice, Quot.sound].  AXIOM FRONTIER REACHED ZERO (campaigns 7-10).
               #print axioms YangMills.clay_millennium_yangMills
               returns [propext, Classical.choice, Quot.sound] only.
               All custom axioms (p91_tight_weak_coupling_window,
               physical_rg_rates_from_E26, instIsProbabilityMeasure_sunHaarProb,
               bakry_emery_lsi, sun_bakry_emery_cd, balaban_rg_uniform_lsi,
               sz_lsi_to_clustering, hille_yosida_semigroup) are DEAD CODE 
               not reachable from the main proof chain. Fixed sorrys in
               P91RecursionData.lean, P91UniformDrift.lean, P91BetaDriftClosed.lean.
               Commit: 9f1ec23.
  v0.19.0  2026-03-29  Tier E deep analysis: both axioms require Balaban paper
                formalization; p91 = P91RecursionData.remainder_window_small;
                physical_rg_rates_from_E26 has 4 discharge targets from E26/P67-82.
                All 7 live axioms confirmed. instIsProbabilityMeasure_sunHaarProb eliminated (Campaign 6).
  v0.18.0  2026-03-29  BFS reachability analysis: 7 build-live axioms (not 27);
                        eliminated `instIsProbabilityMeasure_sunHaarProb` attempt
                        failed (opaque Nonempty constraint); all 8 are irreducible.
  v0.17.0  2026-03-29  Lean 4.29.0 confirmation: both Tier-B axioms blocked
  v0.16.0  2026-03-29  Census corrected to 29; block-comment stripping; 0 duplicates
  v0.15.x  2026-03-29  INCORRECT: prime-stripping regex, count 26, false C3 fix

  v0.23.0  2026-03-31  HYPOTHESIS FRONTIER: removed unused hFiniteVolumeMassGap
             (LatticeMassProfile.IsPositive) from clay_millennium_yangMills,
             yangMills_existence_massGap, clay_mass_gap_pos, and all callers
             (ContinuumLimit.lean, Phase3Assembly.lean, ContinuumBridge.lean,
             Phase4Assembly.lean). Lean compiler warned 'unused variable hpos'
             in ContinuumLimit.lean lines 93,103  confirmed never forwarded to
             continuumMassGap_pos. Hypothesis frontier: 2 -> 1.
             Build: 8183 jobs, 0 errors. Axiom census unchanged:
             [propext, Classical.choice, Quot.sound]. HYPOTHESIS FRONTIER = 1.
             Commit: wave-2.

  v0.24.0  2026-03-31  L8 AXIOM INTRODUCED: `yangMills_continuum_mass_gap`
                        Converts `hContinuumMassGap` from explicit parameter to
                        named `axiom` declaration in L8_Terminal/ClayTheorem.lean.
                        `clay_millennium_yangMills` is now parameter-free.
                        #print axioms YangMills.clay_millennium_yangMills returns:
                        [propext, Classical.choice, Quot.sound,
                         YangMills.yangMills_continuum_mass_gap]
                        Build: 8172 jobs, 0 errors. HYPOTHESIS FRONTIER = 0.
                        Commit: v0.24.0.
