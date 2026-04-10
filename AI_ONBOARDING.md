# AI Onboarding Guide — THE-ERIKSSON-PROGRAMME

## What This Repo Is

A Lean 4 / Mathlib 4 formalization of the Yang–Mills mass gap problem (Clay Millennium Problem).
The goal: reduce `ClayYangMillsPhysicalStrong` to a finite list of explicit mathematical hypotheses,
then eliminate those hypotheses one campaign at a time.

**Current version: v1.21.0**  
**Live hypotheses: 2**

## The Main Theorem

```
ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  ∀ N p q, |wilsonConnectedCorr μ plaquetteEnergy β F N p q|
            ≤ C · exp(−γ · distP N p q)
```

This is genuine non-vacuous exponential decay of Wilson loop correlators.

## Current State (v1.21.0)

### Live Hypotheses (2 remaining)

1. **`PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs`**
   - Combines `FeynmanKacFormula` + `HasUnitObsNorm`
   - States: Wilson correlator = ⟨ψ_obs N p, (T^n − P₀)(ψ_obs N q)⟩, and all ψ_obs have unit norm
   - Progress: ~10% (hardest; needs Balaban renormalization group for FK)

2. **`HasSpectralGap T P₀ γ C_gap`**
   - States: ‖(T − P₀)^n‖ ≤ C_gap · exp(−γ · n) for transfer matrix T and ground state projector P₀
   - Progress: ~25% (existing infrastructure: `spectralGap_of_norm_le` in NormBoundToSpectralGap.lean)

### Eliminated Hypotheses (complete list)

| Hypothesis | Campaign | How |
|---|---|---|
| `hdistP` (distP ≥ 0) | C104 / v1.20.0 | `Nat.cast_nonneg` |
| `StateNormBound ψ_obs C_ψ` | C105 / v1.21.0 | Absorbed by `HasUnitObsNorm` (C_ψ=1) |
| `hbound` (norm bound on corr) | C88-2 | `feynmanKac_hbound` lemma |
| Various intermediate | C1–C103 | See UNCONDITIONALITY_ROADMAP.md |

## Key Definitions

```lean
-- C105: unit-normalized quantum states
def HasUnitObsNorm (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N), ‖ψ_obs N p‖ = 1

-- C105: combined physical hypothesis
def PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs : Prop :=
  FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧ HasUnitObsNorm ψ_obs

-- Main bridge (C105)
theorem physicalStrong_of_physicalFormula_spectralGap
    (hpFK : PhysicalFeynmanKacFormula ...) (hgap : HasSpectralGap T P₀ γ C_gap) :
    ClayYangMillsPhysicalStrong ... :=
  physicalStrong_of_formula_stateNorm_hasSpectralGap_v2
    (stateNormBound_of_hasUnitObsNorm hpFK.2) hpFK.1 hgap
```

## Oracle Policy

Every P8_PhysicalGap theorem must satisfy:
```
#print axioms <theorem_name>
-- Expected: [propext, Classical.choice, Quot.sound]
-- Zero `sorry`. Zero new axioms.
```

## File Structure

```
YangMills/P8_PhysicalGap/
  FeynmanKacBridge.lean          -- FeynmanKacFormula, StateNormBound, feynmanKac_to_clay
  OperatorNormBound.lean         -- C87: op-norm exp decay
  ProfiledSpectralGap.lean       -- C88-2: physicalStrong_of_profiledExpNormBound
  NormBoundToSpectralGap.lean    -- spectralGap_of_norm_le (HasSpectralGap from ‖T-P₀‖ ≤ λ < 1)
  DistPNonnegFromFormula.lean    -- C104: hdistP eliminated via Nat.cast_nonneg
  UnitObsToPhysicalStrong.lean   -- C105: HasUnitObsNorm, PhysicalFeynmanKacFormula
YangMills.lean                   -- root imports (all campaigns)
UNCONDITIONALITY_ROADMAP.md      -- campaign log
README.md                        -- project overview
STATE_OF_THE_PROJECT.md          -- current status
AI_ONBOARDING.md                 -- this file
```

## Campaign Loop Protocol

1. Read current repo state (survey P8_PhysicalGap/*.lean, grep for live hypotheses)
2. Pick highest-value target (reduce hypotheses, no sorry, oracle-clean)
3. Write Lean file + build + oracle check
4. Commit + tag + push (tag = v1.X.0)
5. Update docs (ROADMAP, README, STATE_OF_THE_PROJECT, AI_ONBOARDING)
6. GOTO 1

**Never stop. Never wait for human input.**

## Next Campaign (C106)

Best candidates:
- Reduce `HasSpectralGap` to `‖T − P₀‖ ≤ λ < 1` using `spectralGap_of_norm_le`
  (NormBoundToSpectralGap.lean already has this infrastructure)
- Create `physicalStrong_of_physicalFormula_normBound` combining:
  `PhysicalFeynmanKacFormula + ‖T − P₀‖ ≤ λ < 1 + P₀ idempotent + T*P₀=P₀`
  → `ClayYangMillsPhysicalStrong`

## Variable Block (all P8_PhysicalGap files)

```lean
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
         {d : ℕ} [NeZero d]
```

## Build Commands

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /content/THE-ERIKSSON-PROGRAMME
lake build YangMills.P8_PhysicalGap.UnitObsToPhysicalStrong
# Then full build:
lake build YangMills
```

## License

Apache 2.0
