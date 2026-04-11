# State of the Project — THE-ERIKSSON-PROGRAMME

**Version**: v1.38.0  
**Date**: 2026-04-10  
**Live hypotheses**: 2

## What Has Been Accomplished

The project has reduced `ClayYangMillsPhysicalStrong` — exponential decay of Wilson loop
correlators — to exactly 2 explicit mathematical hypotheses. Every other condition has been
derived or eliminated through 106 campaigns.

## Current Live Hypotheses

### 1. PhysicalFeynmanKacFormula (∼10% done)

```
PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs :=
  FeynmanKacFormula ... ∧ HasUnitObsNorm ψ_obs
```

States that the Wilson correlator equals a quantum mechanical inner product
`⟨ψ_obs N p, (T^n − P₀)(ψ_obs N q)⟩` and all observables have unit norm.
Requires Balaban renormalization group construction. Hardest remaining hypothesis.

### 2. HasNormContraction T P₀ (∼35% done)

```
HasNormContraction T P₀ :=
  P₀ * P₀ = P₀ ∧ T * P₀ = P₀ ∧ P₀ * T = P₀ ∧ 0 < ‖T − P₀‖ ∧ ‖T − P₀‖ < 1
```

States that the transfer matrix T contracts to the ground-state projector P₀
in operator norm. More concrete than the previous `HasSpectralGap` (C106).
Requires constructing T explicitly from the Yang–Mills path integral.

## Recently Eliminated Hypotheses

| Hypothesis | Campaign | Version | Method |
|---|---|---|---|
| `StateNormBound ψ_obs C_ψ` | C105 | v1.21.0 | Absorbed by `HasUnitObsNorm` (C_ψ=1) |
| `hdistP` (distP ≥ 0) | C104 | v1.20.0 | `Nat.cast_nonneg` |
| `HasSpectralGap T P₀ γ C` | C106 | v1.38.0 | Replaced by `HasNormContraction` |

## Main Bridge Theorems

```lean
-- C106: top-level 2-hypothesis theorem
theorem physicalStrong_of_physicalFormula_normContraction
    (hpFK : PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hnc : HasNormContraction T P₀) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP

-- C105: spectral gap version
theorem physicalStrong_of_physicalFormula_spectralGap
    (hpFK : PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hgap : HasSpectralGap T P₀ γ C_gap) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP
```

## Oracle Status

All P8_PhysicalGap theorems: `#print axioms` → `[propext, Classical.choice, Quot.sound]`.
Zero `sorry`. Zero new axioms.

## Progress Estimate

- Overall: ∼27% (2 of ~7.5 effective hypotheses eliminated-to-concrete)
- `HasNormContraction`: ∼35% (operator theory groundwork exists)
- `PhysicalFeynmanKacFormula`: ∼10% (needs Balaban RG)

## Campaign Log Summary

See `UNCONDITIONALITY_ROADMAP.md` for full campaign history (C1–C106).

## C110 (v1.38.0) - FeynmanKacBundle
File: YangMills/L8_Terminal/FeynmanKacBundle.lean
Bundles FeynmanKacFormula + StateNormBound + HasSpectralGap + distP_nonneg into a single Prop (FeynmanKacBundle), with physicalStrong_of_feynmanKacBundle : FeynmanKacBundle -> ClayYangMillsPhysicalStrong. Oracle: [propext, Classical.choice, Quot.sound]. Zero sorry.

## C111 (v1.38.0) - ClayStrongFromFeynmanKac
File: YangMills/L8_Terminal/ClayStrongFromFeynmanKac.lean
Adds clayStrong_of_feynmanKacBundle : FeynmanKacBundle -> ClayYangMillsStrong via feynmanKac_to_strong. Oracle: [propext, Classical.choice, Quot.sound]. Zero sorry.

## C122 (v1.38.0) - ClayStrongFromFeynmanKacTheoremBundle
File: YangMills/L8_Terminal/VacuumAdjointFixed.lean
physicalStrong_of_projectedOpNormBound_rankOneVacuum_selfAdjoint: FK strong path via VacuumAdjointFixed + FeynmanKacOpNormFromFormula. Oracle: [propext, Classical.choice, Quot.sound, yangMills_continuum_mass_gap].

## C123 (v1.39.0) - sun_physical_mass_gap [STRATEGY SHIFT]
Files: YangMills/P8_PhysicalGap/PhysicalMassGap.lean, YangMills.lean
**ELIMINATES yangMills_continuum_mass_gap entirely.**
Integrated full P8_PhysicalGap LSI pipeline (49 modules). sun_physical_mass_gap proves ClayYangMillsTheorem via independent route: Balaban RG -> DLR-LSI -> Stroock-Zegarlinski -> clustering -> mass gap.
Oracle: [propext, Classical.choice, Quot.sound, YangMills.~~bakry_emery_lsi~~ **ELIMINATED C124**, YangMills.~~balaban_rg_uniform_lsi~~ **ELIMINATED C127**, YangMills.~~sun_bakry_emery_cd~~ **ELIMINATED C126**, YangMills.~~sz_lsi_to_clustering~~ **ELIMINATED C125**].
No yangMills_continuum_mass_gap. Zero sorry. This is the new primary proof path.

## Current Frontier (C124+)
4 remaining Yang-Mills-specific axioms in sun_physical_mass_gap:
- YangMills.~~bakry_emery_lsi~~ **ELIMINATED C124** (BalabanToLSI.lean:61)
- YangMills.~~sun_bakry_emery_cd~~ **ELIMINATED C126** (BalabanToLSI.lean:71)
- YangMills.~~balaban_rg_uniform_lsi~~ **ELIMINATED C127** (BalabanToLSI.lean:102)
- YangMills.~~sz_lsi_to_clustering~~ **ELIMINATED C125** (BalabanToLSI.lean:127)
Each proven from Mathlib primitives eliminates one axiom.
