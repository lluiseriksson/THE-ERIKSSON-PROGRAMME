# AXIOM_FRONTIER.md — THE-ERIKSSON-PROGRAMME
<!-- Version: v0.16.0  (2026-03-29) -->
<!-- Corrected axiom count: 29 unique names. -->
<!-- Previous v0.15.x counted 26 due to prime-stripping regex bug. -->

## Summary

| Metric | Value |
|--------|-------|
| Unique axiom names (all files) | **29** |
| Genuine duplicates (same name, multiple files) | 0 |
| Tier A (structural, should not exist) | 0 |
| Tier B (Mathlib close — may close next) | 3 |
| Tier C (Mathlib infra gap — C₀-semigroup) | 7 |
| Tier D (genuine open math) | 5 |
| Tier E (ClayCore/BalabanRG — quantitative) | 4 |
| Tier F (LieSUN experimental spike) | 10 |

---

## Axiom Inventory (29 total)

### Tier B — Mathlib-closeable candidates

These axioms may be dischargeable with currently available Mathlib lemmas.
Each requires a `lake build` confirmation before the axiom is declared closed.

| Name | File | Strategy |
|------|------|----------|
| `matExp_traceless_det_one` | LieExpCurve.lean:76 | `Matrix.det_exp` + `Matrix.trace_smul` |
| `instIsTopologicalGroupSUN` | SUN_StateConstruction.lean:78 | Subgroup topology inheritance |
| `instIsProbabilityMeasure_sunHaarProb` (concrete) | SUN_StateConstruction.lean:107 | Already proved via `Measure.haarMeasure_self` |

**NOTE**: `instIsProbabilityMeasure_sunHaarProb` in BalabanToLSI.lean:48 is for
an **opaque abstract** `sunHaarProb` and CANNOT be closed with `inferInstance`.
The concrete IsProbabilityMeasure proof in SUN_StateConstruction.lean is separate
and is already proved (not an axiom).

---

### Tier C — C₀-semigroup Mathlib gap (7 axioms)

All 7 of these are blocked by the absence of C₀-semigroup / generator theory
from Mathlib4 (as of the repo's pinned Mathlib version).  Gronwall IS available
in Mathlib4, but does not help here because the actual blocker is constructing
the infinitesimal generator `L` and proving ContinuousOn / HasDerivWithinAt for
`t ↦ Var(T_t f)` — which requires C₀-semigroup formalism.

| Name | File |
|------|------|
| `hille_yosida_core` | HilleYosidaDecomposition.lean:62 |
| `poincare_to_variance_decay` | HilleYosidaDecomposition.lean:69 |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | VarianceDecayFromPoincare.lean:79 |
| `gronwall_variance_decay` | VarianceDecayFromPoincare.lean:133 |
| `hille_yosida_semigroup` | MarkovSemigroupDef.lean:126 |
| `poincare_to_covariance_decay` | StroockZegarlinski.lean:21 |
| `sun_variance_decay` | SUN_LiebRobin.lean:41 |

---

### Tier D — Genuine open mathematics (5 axioms)

| Name | File | Note |
|------|------|------|
| `bakry_emery_lsi` | BalabanToLSI.lean:63 | BE theory not in Mathlib |
| `sun_bakry_emery_cd` | BalabanToLSI.lean:73 | SU(N) Bakry-Émery CD(N/4,∞) — Clay core |
| `balaban_rg_uniform_lsi` | BalabanToLSI.lean:102 | Balaban RG LSI promotion — Clay core |
| `sun_lieb_robinson_bound` | SUN_LiebRobin.lean:47 | Lieb-Robinson for SU(N) lattice — Clay core |
| `sz_lsi_to_clustering` | BalabanToLSI.lean:126 | Abstract interface: LSI → clustering |

---

### Tier E — ClayCore/BalabanRG quantitative (4 axioms)

| Name | File | Note |
|------|------|------|
| `blockFinset` | FiniteBlocks.lean:17 | Finset over lattice block |
| `blockFinset_spec` | FiniteBlocks.lean:20 | Block membership characterisation |
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow.lean:51 | Quantitative RG bound |
| `physical_rg_rates_from_E26` | PhysicalRGRates.lean:101 | Physical RG rate estimates |

---

### Tier F — LieSUN experimental spike (10 axioms)

These are in `YangMills/Experimental/LieSUN/` files.  They form two separate
namespaces:

**Unprimed (canonical) — LieDerivativeRegularity.lean + LieDerivReg_v4.lean**:

| Name | File |
|------|------|
| `generatorMatrix` | LieDerivativeRegularity.lean:18 |
| `gen_skewHerm` | LieDerivativeRegularity.lean:20 |
| `gen_trace_zero` | LieDerivativeRegularity.lean:22 |
| `sunGeneratorData` | LieDerivReg_v4.lean:26 |
| `lieDerivReg_all` | LieDerivReg_v4.lean:43 |

**Primed (experimental spike v3) — DirichletConcrete.lean**:

> These axioms (`generatorMatrix'`, `gen_skewHerm'`, `gen_trace_zero'`) are
> DISTINCT from the unprimed ones above.  The prime suffix is part of the Lean
> identifier.  DirichletConcrete.lean is a "Spike v3" experimental file that
> maintains its own copy of the generator bundle under primed names, used by
> `lieDeriv` and `IsDiffAlong` definitions in the same file.
>
> ⚠️  Do NOT delete these primed axioms — DirichletConcrete.lean depends on them.

| Name | File |
|------|------|
| `generatorMatrix'` | DirichletConcrete.lean:23 |
| `gen_skewHerm'` | DirichletConcrete.lean:26 |
| `gen_trace_zero'` | DirichletConcrete.lean:29 |
| `dirichlet_lipschitz_contraction` | DirichletContraction.lean:55 |
| `sunDirichletForm_contraction` | SUN_DirichletCore.lean:178 |

---

## Regression Warning: False Duplicate Bug (v0.15.x)

The census regex in v0.15.x used `\baxiom\s+(\w+)` which treats `'`
(apostrophe) as a non-word character.  This caused `generatorMatrix'` to match
as `generatorMatrix`, creating a false "duplicate" across DirichletConcrete.lean
and LieDerivativeRegularity.lean.

The `elimination_structural_v1.py` script acted on this false duplicate by:
1. Deleting the 3 primed axioms from DirichletConcrete.lean
2. Adding an import for LieDerivativeRegularity.lean

This broke DirichletConcrete.lean locally (undefined primed identifier
references in `lieDeriv`, `IsDiffAlong`, etc.).  The push to GitHub failed
(credential URL bug), so GitHub remained intact.

**fix_regression_v2.py** corrects all three issues:
- Reverts DirichletConcrete.lean from GitHub HEAD
- Replaces census regex with prime-aware `[\w']+` pattern
- Fixes git auth to use idempotent URL reset

---

## Change Log

| Version | Date | Summary |
|---------|------|---------|
| v0.16.0 | 2026-03-29 | Corrected count 29 (was 26); false dup removed; prime-aware census |
| v0.15.x | 2026-03-29 | Incorrect; prime-stripping regex; false C3 fix applied |
| v0.14.x | 2026-03-28 | Initial structural census |
