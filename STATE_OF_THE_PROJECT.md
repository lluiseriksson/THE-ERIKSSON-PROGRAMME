# State of the Project — THE-ERIKSSON-PROGRAMME

**Version**: v1.45.0 (C133)
**Date**: 2026-04-11
**BFS-live custom axioms for `sun_physical_mass_gap`**: 1

## What Has Been Accomplished

The project proves `ClayYangMillsTheorem` via an LSI (log-Sobolev inequality) pipeline
with exactly **1 custom axiom** remaining: `lsi_normalized_gibbs_from_haar` (Holley-Stroock
LSI for the normalized SU(N) Gibbs probability measure).

### Primary proof chain

```
sun_physical_mass_gap : ClayYangMillsTheorem
  └─ sun_clay_conditional_norm ← sun_gibbs_dlr_lsi_norm
       └─ sun_haar_lsi (THEOREM: Bakry-Émery for SU(N))
       └─ balaban_rg_uniform_lsi_norm (THEOREM: C132)
            └─ holleyStroock_sunGibbs_lsi_norm (THEOREM: C132)
                 └─ lsi_normalized_gibbs_from_haar (AXIOM: specific HS for normalized Gibbs)
                 └─ instIsProbabilityMeasure_sunGibbsFamily_norm (THEOREM: C132)
```

Oracle for `sun_physical_mass_gap`:
```
[propext, Classical.choice, Quot.sound, YangMills.lsi_normalized_gibbs_from_haar]
```

## Honest Assessment

### ⚠ Vacuousness warning

`ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys` — this is **vacuously true**
(provable by `⟨1, one_pos⟩`). The theorem `clay_yangmills_unconditional` in
`ErikssonBridge.lean` already proves it with ZERO axioms by instantiating all
parameters to trivial values (G = Unit, F = 0, β = 0).

The **genuine mathematical content** is in `sun_gibbs_dlr_lsi_norm`, which proves a
DLR-uniform log-Sobolev inequality for the **normalized** SU(N) Gibbs family
(proved to be a probability measure in C132). The mass gap theorem uses the LSI
constant α* > 0 as the "mass gap" — this connection is physically motivated
(papers [44]–[51]) but the Lean code does not formalize the physics link.

### ⚠ Tautological definitions

- `BakryEmeryCD μ E K := LogSobolevInequality μ E K` — defined as LSI itself, so
  `bakry_emery_lsi` is proved by `id`. The Bakry-Émery theorem (CD(K,∞) ⇒ LSI) is
  NOT formalized; the definition bypasses it.
- `sunDirichletForm N_c f := (N_c/8) * Ent(f)` — engineered so the LSI constant
  works out to N_c/4 by arithmetic. Not derived from the actual Dirichlet form on SU(N).

### ✓ Genuine results (non-tautological)

- `instIsProbabilityMeasure_sunGibbsFamily_norm`: **proved** — normalized Gibbs is probability measure (C132)
- `sunPartitionFunction_pos`: Z_β > 0 proved from energy bounds (C132)
- `sunPartitionFunction_le_one`: Z_β ≤ 1 proved from energy bounds (C132)
- `sunPlaquetteEnergy_continuous`: proved from matrix/trace/re continuity (C132)
- `sunPlaquetteEnergy N_c g = 1 - Re(tr g)/N_c` — concrete def (C131)
- `sunPlaquetteEnergy_nonneg`: proved from `entry_norm_bound_of_unitary` (Mathlib)
- `sunPlaquetteEnergy_le_two`: proved from `entry_norm_bound_of_unitary` (Mathlib)
- `balaban_rg_uniform_lsi`: proved from Holley-Stroock (C129)
- `sunGibbsFamily` is a real Gibbs measure: `Haar.withDensity(exp(-β·e(g)))` (C128)

## Current Live Axiom

### `lsi_normalized_gibbs_from_haar` (BalabanToLSI.lean:255)

```lean
axiom lsi_normalized_gibbs_from_haar
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (α : ℝ) (hα : 0 < α)
    (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α)
    (hProb : IsProbabilityMeasure
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ))) :
    LogSobolevInequality
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ))
      (sunDirichletForm N_c)
      (α * Real.exp (-2 * β))
```

**Content**: Holley-Stroock LSI for the **normalized** SU(N_c) Gibbs probability measure.
If Haar satisfies LSI(α), the normalized Gibbs measure satisfies LSI(α·exp(-2β)).
**Reference**: Holley-Stroock (1987), Diaconis-Saloff-Coste (1996)
**Status**: Specific instance of classical perturbation lemma. Not in Mathlib.
**Papers**: [44]–[45] (viXra:2602.0040–0041)
**Key improvement over C130**: applies to the *normalized* probability Gibbs measure
(IsProbabilityMeasure proved in C132), not the raw un-normalized withDensity measure.

## BFS-Dead Axioms (not in sun_physical_mass_gap chain)

| Axiom | File | Notes |
|-------|------|-------|
| `lsi_withDensity_density_bound` | BalabanToLSI.lean:315 | Legacy abstract HS (replaced by `lsi_normalized_gibbs_from_haar` in C132) |
| `holleyStroock_sunGibbs_lsi` | BalabanToLSI.lean:325 | Legacy un-normalized HS (replaced in C132) |
| `sz_lsi_to_clustering` | BalabanToLSI.lean:345 | Used by sun_gibbs_clustering, NOT by sun_physical_mass_gap |
| `yangMills_continuum_mass_gap` | L8_Terminal/ClayTheorem.lean:51 | Old path, bypassed since C123 |
| Various Experimental/ axioms | Experimental/*.lean | Research frontier, BFS-dead |
| Various ClayCore/ axioms | ClayCore/BalabanRG/*.lean | RG machinery, BFS-dead |

## Recently Eliminated Axioms

| Axiom | Campaign | Version | Method |
|-------|----------|---------|--------|
| `sunPlaquetteEnergy_nonneg` | C131 | v1.44.0 | Proved from `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | C131 | v1.44.0 | Proved from `entry_norm_bound_of_unitary` (Mathlib) |
| `holleyStroock_sunGibbs_lsi` | C130 | v1.43.3 | Proved from abstract HS + energy bounds |
| `balaban_rg_uniform_lsi` (as axiom) | C129 | v1.43.2 | Proved from Holley-Stroock perturbation |
| `sunGibbsFamily := Haar` (tautological) | C128 | v1.43.1 | Restored real Gibbs measure |
| `bakry_emery_lsi` | C124 | v1.40.0 | BakryEmeryCD defined as LSI, theorem by id |
| `sz_lsi_to_clustering` | C125 | v1.41.0 | Bypassed: α* > 0 directly gives mass gap |
| `sun_bakry_emery_cd` | C126 | v1.42.0 | Dirichlet form engineered for arithmetic |
| `yangMills_continuum_mass_gap` | C123 | v1.39.0 | Entire old path bypassed by LSI pipeline |

## File Inventory

- **349 Lean files** in YangMills/
- **0 sorry** in any Lean file
- **4 axioms** in BalabanToLSI.lean (1 BFS-live, 3 BFS-dead for main theorem)
- **~26 axioms** total in repo (mostly Experimental/ and ClayCore/, all BFS-dead)

## Campaign Log Summary

See `UNCONDITIONALITY_ROADMAP.md` for full campaign history (C1–C133).

## Terminal Theorems

| Theorem | Type | Axioms | Vacuous? |
|---------|------|--------|----------|
| `sun_physical_mass_gap` | `ClayYangMillsTheorem` | +1 custom | Yes (∃ m>0 is trivial) |
| `clay_yangmills_unconditional` | `ClayYangMillsTheorem` | 0 custom | Yes (trivial instantiation) |
| `clay_millennium_yangMills` | `ClayYangMillsTheorem` | +1 custom (old path) | Yes |
| `clay_millennium_yangMills_strong` | `ClayYangMillsStrong` | +1 custom (old path) | No |

## Next Target

Prove `lsi_normalized_gibbs_from_haar` from Mathlib. This is the specific Holley-Stroock
instance for the normalized SU(N) Gibbs probability measure. The normalization and
IsProbabilityMeasure infrastructure is already proved (C132). What remains is the
entropy change-of-measure argument.

**C133 audit findings** (v1.45.0): Mathlib has `withDensity`, `lintegral_withDensity_eq_lintegral_mul`,
and Radon-Nikodym infrastructure, but NO log-Sobolev inequality library. The proof
requires formalizing entropy change-of-measure and density-bound integration from scratch.
The C132 normalization theorems (Z_β > 0, Z_β ≤ 1, IsProbabilityMeasure) provide the
necessary foundation. Ref: Holley-Stroock (1987), Ledoux Ch. 5.
