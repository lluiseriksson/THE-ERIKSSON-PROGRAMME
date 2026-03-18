# AXIOM FRONTIER — THE-ERIKSSON-PROGRAMME v0.8.41

Last updated: v0.8.41 (SUN_DirichletCore import cycle resolved)

## Summary

| Count | Category |
|-------|----------|
| 1 | Physics (new mathematics) |
| 7 | Mathlib infrastructure gaps |
| 1 | Clay core |

---

## Physics axioms (genuine new mathematics)

These are NOT software gaps. They represent physical content that must be
supplied by the E26 paper series.

| Axiom | File | Reference | Removal path |
|-------|------|-----------|--------------|
| `sun_lieb_robinson_bound` | SUN_LiebRobin | Hastings-Koma 2006 | E26 papers (P76+) |

---

## Mathlib infrastructure gaps

These will be eliminated as Mathlib matures. None of these represent
new mathematics — the proofs exist in the literature.

| Axiom | File | Gap description | Removal path |
|-------|------|-----------------|--------------|
| `hille_yosida_semigroup` | MarkovSemigroupDef | C₀-semigroup / Beurling-Deny | Mathlib C₀-semigroup theory |
| `instIsTopologicalGroupSUN` | SUN_StateConstruction | specialUnitaryGroup is Submonoid of Matrix (not Subgroup of unitaryGroup); topology inheritance not automatic | Mathlib LieGroup API for SU(N) |
| `instFintypeLieGenIndex` | SUN_DirichletCore | su(N) basis has N²-1 elements; requires Lie algebra dimension theorem | Mathlib LieAlgebra fintype |
| `lieDerivative_linear` | SUN_DirichletCore | Directional derivatives are linear; requires ContMDiff on SU(N) | Mathlib LieGroup + ModelWithCorners |
| `lieDerivative_const` | SUN_DirichletCore | Directional derivatives kill constants | Same as above |
| `sunDirichletForm_subadditive` | SUN_DirichletCore | (a+b)² ≤ 2a²+2b²; integral_mono requires Measurable on opaque lieDerivative | fun_prop on opaque defs |
| `sunDirichletForm_contraction` | SUN_DirichletCore | Beurling-Deny / normal contraction; chain rule for Lipschitz functions | Mathlib LieGroup + Rademacher |

---

## Clay core

This is the mathematical heart of the Yang-Mills mass gap problem.

| Axiom | File | Description |
|-------|------|-------------|
| `balaban_rg_uniform_lsi` | BalabanToLSI | Uniform LSI from Balaban renormalization group. This is the Clay problem core. |

---

## Architecture milestones

### v0.8.41 — Import cycle resolved
- `SUN_DirichletCore.lean`: new cycle-free module
  - Contains: `sunDirichletForm_concrete`, `lieDerivative`, `sunDirichletForm_isDirichletFormStrong`
  - Imports: `SUN_StateConstruction` + `LSIDefinitions` only
  - Does NOT import: `LSItoSpectralGap` (which caused the cycle)
- `sunMarkovSemigroup`: **promoted from axiom to def**
  - Now: `hille_yosida_semigroup (sunDirichletForm_concrete N_c) (sunDirichletForm_isDirichletFormStrong)`
  - Before: bare axiom

### v0.8.35 — SUN_Compact proved
- `isCompact_specialUnitaryGroup`: proved via `entry_norm_bound_of_unitary` (Mathlib)
- `instCompactSpaceSUN_concrete`: proved instance

### v0.8.32 — SpatialLocalityFramework
- 0 sorrys, 0 axioms
- `dynamic_covariance_at_optimalTime`: proved
- `locality_to_static_covariance_v2`: proved

## Axioms removed since v0.8.29

| Axiom | Version | How removed |
|-------|---------|-------------|
| `sunMarkovSemigroup` | v0.8.41 | Import cycle broken via SUN_DirichletCore |
| `locality_to_static_covariance_v1` | v0.8.32 | Replaced by v2 (deprecated) |
| `instCompactSpaceSUN` | v0.8.35 | Proved via entry_norm_bound_of_unitary |
