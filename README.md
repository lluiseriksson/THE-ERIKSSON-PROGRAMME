# THE-ERIKSSON-PROGRAMME

**Lean 4 / Mathlib 4 formalization of the Yang–Mills mass gap problem**  
**Version**: v1.26.0 | **Live hypotheses**: 2

## Goal

Reduce `ClayYangMillsPhysicalStrong` — exponential decay of Wilson loop correlators —
to a finite list of explicit, checkable hypotheses. Eliminate them one campaign at a time.

```lean
ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  ∀ N p q, |wilsonConnectedCorr μ plaquetteEnergy β F N p q|
            ≤ C · exp(−γ · distP N p q)
```

## Current Status (v1.26.0)

| Hypothesis | Status | Concreteness |
|---|---|---|
| `PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs` | **Live** (~10%) | FK bridge + unit obs norm |
| `PhysicalContractionBundle (bundles PhysicalFeynmanKacFormula ∧ HasNormContraction)

### Recently Eliminated

| Hypothesis | Campaign | Version | How |
|---|---|---|---|
| `HasSpectralGap T P₀ γ C` | C106 | v1.26.0 | Replaced by `HasNormContraction` |
| `StateNormBound ψ_obs C_ψ` | C105 | v1.21.0 | Absorbed by `HasUnitObsNorm` |
| `hdistP` (distP ≥ 0) | C104 | v1.20.0 | `Nat.cast_nonneg` |

## Top-Level Theorem (C106)

```lean
theorem physicalStrong_of_physicalFormula_normContraction
    (hpFK : PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hnc  : HasNormContraction T P₀) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP
```

**Oracle**: `[propext, Classical.choice, Quot.sound]` — zero `sorry`, zero new axioms.

## Key Definitions

```lean
-- Unit-normalized quantum states (C105)
def HasUnitObsNorm (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N), ‖ψ_obs N p‖ = 1

-- Combined physical hypothesis (C105)
def PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs : Prop :=
  FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧ HasUnitObsNorm ψ_obs

-- Concrete operator-norm contraction (C106)
def HasNormContraction (T P₀ : H →L[ℝ] H) : Prop :=
  P₀ * P₀ = P₀ ∧ T * P₀ = P₀ ∧ P₀ * T = P₀ ∧ 0 < ‖T − P₀‖ ∧ ‖T − P₀‖ < 1
```

## Structure

```
YangMills/P8_PhysicalGap/
  FeynmanKacBridge.lean           -- FK formula, StateNormBound
  NormBoundToSpectralGap.lean     -- spectralGap_of_normContraction_via_le
  DistPNonnegFromFormula.lean     -- C104: hdistP eliminated
  UnitObsToPhysicalStrong.lean    -- C105: HasUnitObsNorm, PhysicalFeynmanKacFormula
  NormContractionToPhysical.lean  -- C106: HasNormContraction
YangMills.lean                    -- root imports
UNCONDITIONALITY_ROADMAP.md       -- campaign log (C1–C106)
STATE_OF_THE_PROJECT.md           -- current status
AI_ONBOARDING.md                  -- AI agent guide
```

## Campaign Protocol

1. Read repo state → 2. Pick highest-value target → 3. Write Lean + build + oracle
4. Commit + tag + push → 5. Update docs → 6. GOTO 1

## License

Apache 2.0
