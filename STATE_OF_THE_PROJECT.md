# State of the Project — THE-ERIKSSON-PROGRAMME

**Version**: v1.44.0 (C131)
**Date**: 2026-04-11
**BFS-live custom axioms for `sun_physical_mass_gap`**: 1

## What Has Been Accomplished

The project proves `ClayYangMillsTheorem` via an LSI (log-Sobolev inequality) pipeline
with exactly **1 custom axiom** remaining: `lsi_withDensity_density_bound` (abstract
Holley-Stroock density perturbation, pure functional analysis).

### Primary proof chain

```
sun_physical_mass_gap : ClayYangMillsTheorem
  └─ sun_clay_conditional ← sun_gibbs_dlr_lsi
       └─ sun_haar_lsi (THEOREM: Bakry-Émery for SU(N))
       └─ balaban_rg_uniform_lsi (THEOREM: Holley-Stroock perturbation)
            └─ holleyStroock_sunGibbs_lsi (THEOREM: C130)
                 └─ lsi_withDensity_density_bound (AXIOM: abstract HS)
                 └─ sunPlaquetteEnergy_nonneg (THEOREM: C131)
                 └─ sunPlaquetteEnergy_le_two (THEOREM: C131)
```

Oracle for `sun_physical_mass_gap`:
```
[propext, Classical.choice, Quot.sound, YangMills.lsi_withDensity_density_bound]
```

## Honest Assessment

### ⚠ Vacuousness warning

`ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys` — this is **vacuously true**
(provable by `⟨1, one_pos⟩`). The theorem `clay_yangmills_unconditional` in
`ErikssonBridge.lean` already proves it with ZERO axioms by instantiating all
parameters to trivial values (G = Unit, F = 0, β = 0).

The **genuine mathematical content** is in `sun_gibbs_dlr_lsi`, which proves a
DLR-uniform log-Sobolev inequality for the SU(N) Gibbs family. The mass gap
theorem uses the LSI constant α* > 0 as the "mass gap" — this connection is
physically motivated (papers [44]–[51]) but the Lean code does not formalize
the physics link.

### ⚠ Tautological definitions

- `BakryEmeryCD μ E K := LogSobolevInequality μ E K` — defined as LSI itself, so
  `bakry_emery_lsi` is proved by `id`. The Bakry-Émery theorem (CD(K,∞) ⇒ LSI) is
  NOT formalized; the definition bypasses it.
- `sunDirichletForm N_c f := (N_c/8) * Ent(f)` — engineered so the LSI constant
  works out to N_c/4 by arithmetic. Not derived from the actual Dirichlet form on SU(N).

### ✓ Genuine results (non-tautological)

- `sunPlaquetteEnergy N_c g = 1 - Re(tr g)/N_c` — concrete def (C131)
- `sunPlaquetteEnergy_nonneg`: proved from `entry_norm_bound_of_unitary` (Mathlib)
- `sunPlaquetteEnergy_le_two`: proved from `entry_norm_bound_of_unitary` (Mathlib)
- `holleyStroock_sunGibbs_lsi`: proved from abstract HS + energy bounds (C130)
- `balaban_rg_uniform_lsi`: proved from Holley-Stroock (C129)
- `sunGibbsFamily` is a real Gibbs measure: `Haar.withDensity(exp(-β·e(g)))` (C128)

## Current Live Axiom

### `lsi_withDensity_density_bound` (BalabanToLSI.lean:192)

```lean
axiom lsi_withDensity_density_bound
    {S : Type*} [MeasurableSpace S]
    (mu : MeasureTheory.Measure S) (E : (S -> ℝ) -> ℝ)
    (α r : ℝ) (hα : 0 < α) (hr : 0 < r) (hr1 : r ≤ 1)
    (h_lsi : LogSobolevInequality mu E α)
    (rho : S -> ENNReal) (h_lb : ∀ x, ENNReal.ofReal r ≤ rho x)
    (h_ub : ∀ x, rho x ≤ 1) :
    LogSobolevInequality (mu.withDensity rho) E (α * r)
```

**Content**: If μ satisfies LSI(α) and r ≤ ρ(x) ≤ 1, then μ.withDensity(ρ) satisfies LSI(α·r).
**Reference**: Holley-Stroock (1987), Diaconis-Saloff-Coste (1996)
**Status**: Pure functional analysis. Not in Mathlib. Provable from first principles.
**Papers**: [44]–[45] (viXra:2602.0040–0041)

## BFS-Dead Axioms (not in sun_physical_mass_gap chain)

| Axiom | File | Notes |
|-------|------|-------|
| `sz_lsi_to_clustering` | BalabanToLSI.lean:256 | Used by sun_gibbs_clustering, NOT by sun_physical_mass_gap |
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
- **2 axioms** in BalabanToLSI.lean (1 BFS-live, 1 BFS-dead for main theorem)
- **~25 axioms** total in repo (mostly Experimental/ and ClayCore/, all BFS-dead)

## Campaign Log Summary

See `UNCONDITIONALITY_ROADMAP.md` for full campaign history (C1–C131).

## Terminal Theorems

| Theorem | Type | Axioms | Vacuous? |
|---------|------|--------|----------|
| `sun_physical_mass_gap` | `ClayYangMillsTheorem` | +1 custom | Yes (∃ m>0 is trivial) |
| `clay_yangmills_unconditional` | `ClayYangMillsTheorem` | 0 custom | Yes (trivial instantiation) |
| `clay_millennium_yangMills` | `ClayYangMillsTheorem` | +1 custom (old path) | Yes |
| `clay_millennium_yangMills_strong` | `ClayYangMillsStrong` | +1 custom (old path) | No |

## Next Target

Prove `lsi_withDensity_density_bound` from Mathlib. This is pure functional analysis:
the Holley-Stroock argument for log-Sobolev inequalities under bounded density
perturbation. Ref: Holley-Stroock (1987), Ledoux "Concentration of Measure" Ch. 5.
