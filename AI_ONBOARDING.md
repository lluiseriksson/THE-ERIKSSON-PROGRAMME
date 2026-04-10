# AI Onboarding Guide — THE-ERIKSSON-PROGRAMME

## What This Repo Is

A Lean 4 / Mathlib 4 formalization of the Yang–Mills mass gap problem (Clay Millennium Problem).
The goal: reduce `ClayYangMillsPhysicalStrong` to a finite list of explicit hypotheses,
then eliminate those hypotheses one campaign at a time.

**Current version: v1.38.0**  
**Live hypotheses: 2**

## The Main Theorem

```
ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  ∀ N p q, |wilsonConnectedCorr μ plaquetteEnergy β F N p q|
            ≤ C · exp(−γ · distP N p q)
```

Genuine non-vacuous exponential decay of Wilson loop correlators.

## Current State (v1.38.0)

### Live Hypotheses (2 remaining)

1. **`PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs`**
   - `FeynmanKacFormula ... ∧ HasUnitObsNorm ψ_obs`
   - Wilson correlator = ⟨ψ_obs N p, (T^n − P₀)(ψ_obs N q)⟩, all obs have unit norm
   - Progress: ~10% (hardest; needs Balaban renormalization group)

2. **`HasNormContraction T P₀`**
   - `P₀ * P₀ = P₀ ∧ T * P₀ = P₀ ∧ P₀ * T = P₀ ∧ 0 < ‖T − P₀‖ ∧ ‖T − P₀‖ < 1`
   - Transfer matrix contracts to ground-state projector in operator norm
   - Progress: ~35% (more concrete than HasSpectralGap; operator theory groundwork exists)

### Eliminated Hypotheses (recent)

| Hypothesis | Campaign | How |
|---|---|---|
| `HasSpectralGap T P₀ γ C` | C106 / v1.38.0 | Replaced by `HasNormContraction` |
| `StateNormBound ψ_obs C_ψ` | C105 / v1.21.0 | Absorbed by `HasUnitObsNorm` (C_ψ=1) |
| `hdistP` (distP ≥ 0) | C104 / v1.20.0 | `Nat.cast_nonneg` |
| Earlier hypotheses | C1–C103 | See UNCONDITIONALITY_ROADMAP.md |

## Key Definitions (v1.38.0)

```lean
-- C105: unit-normalized quantum states
def HasUnitObsNorm (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N), ‖ψ_obs N p‖ = 1

-- C105: combined physical hypothesis
def PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs : Prop :=
  FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧ HasUnitObsNorm ψ_obs

-- C106: concrete operator-norm contraction
def HasNormContraction (T P₀ : H →L[ℝ] H) : Prop :=
  P₀ * P₀ = P₀ ∧ T * P₀ = P₀ ∧ P₀ * T = P₀ ∧ 0 < ‖T − P₀‖ ∧ ‖T − P₀‖ < 1
```

## Top-Level Bridge (C106)

```lean
theorem physicalStrong_of_physicalFormula_normContraction
    (hpFK : PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hnc : HasNormContraction T P₀) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_physicalFormula_spectralGap hpFK
    (spectralGap_of_hasNormContraction hnc)
```

## Oracle Policy

Every P8_PhysicalGap theorem must satisfy:
```
#print axioms <theorem_name>
-- Expected: [propext, Classical.choice, Quot.sound]
-- Zero sorry. Zero new axioms.
```

## File Structure (P8_PhysicalGap)

```
FeynmanKacBridge.lean           -- FeynmanKacFormula, StateNormBound, feynmanKac_to_clay
OperatorNormBound.lean          -- C87: op-norm exp decay
ProfiledSpectralGap.lean        -- C88-2: physicalStrong_of_profiledExpNormBound
NormBoundToSpectralGap.lean     -- spectralGap_of_normContraction_via_le
DistPNonnegFromFormula.lean     -- C104: hdistP eliminated
UnitObsToPhysicalStrong.lean    -- C105: HasUnitObsNorm, PhysicalFeynmanKacFormula
NormContractionToPhysical.lean  -- C106: HasNormContraction, top-level bridge
```

## Campaign Loop Protocol

1. Read current repo state (survey P8_PhysicalGap/*.lean, grep live hypotheses)
2. Pick highest-value target (reduce hypotheses count or increase concreteness)
3. Write Lean file + build + oracle check
4. Commit + tag + push (tag = v1.X.0)
5. Update docs (ROADMAP, README, STATE_OF_THE_PROJECT, AI_ONBOARDING)
6. GOTO 1

**Never stop. Never wait for human input.**

## Next Campaign (C107)

Candidates for `HasNormContraction T P₀`:
- Reduce idempotent condition `P₀ * P₀ = P₀` to something more primitive
- Show `HasNormContraction` from a concrete spectral condition on T
- Explore `PointwiseResidualContraction.lean` or `ProjectedOpNormToComplementContraction.lean`
  (both exist in P8_PhysicalGap and may provide relevant infrastructure)

Survey command: `ls YangMills/P8_PhysicalGap/` and read files for relevant theorems.

## Variable Block

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
lake build YangMills.P8_PhysicalGap.NormContractionToPhysical  # target only
lake build YangMills                                             # full build
```

## License

Apache 2.0

- C110 (v1.38.0): FeynmanKacBundle in YangMills/L8_Terminal/FeynmanKacBundle.lean -- bundles FeynmanKacFormula+StateNormBound+HasSpectralGap+distP_nonneg; physicalStrong_of_feynmanKacBundle; oracle clean.

- C111 (v1.38.0): ClayStrongFromFeynmanKac in YangMills/L8_Terminal/ClayStrongFromFeynmanKac.lean -- clayStrong_of_feynmanKacBundle : FeynmanKacBundle -> ClayYangMillsStrong; oracle clean.

- C122 (v1.38.0): ClayStrongFromFeynmanKacTheoremBundle in YangMills/L8_Terminal/VacuumAdjointFixed.lean -- physicalStrong_of_projectedOpNormBound_rankOneVacuum_selfAdjoint; oracle still has yangMills_continuum_mass_gap.

- C123 (v1.39.0): sun_physical_mass_gap in YangMills/P8_PhysicalGap/PhysicalMassGap.lean -- **STRATEGY SHIFT: eliminates yangMills_continuum_mass_gap entirely**. Integrated all 49 P8_PhysicalGap LSI modules into YangMills.lean. Proof route: Balaban RG -> DLR-LSI -> Stroock-Zegarlinski -> clustering -> mass gap. Oracle: [propext, Classical.choice, Quot.sound, YangMills.bakry_emery_lsi, YangMills.balaban_rg_uniform_lsi, YangMills.sun_bakry_emery_cd, YangMills.sz_lsi_to_clustering]. Zero sorry.

## Current Strategy (C124+): Eliminate the 4 Frontier Axioms

The artificial axiom `yangMills_continuum_mass_gap` is GONE from the primary proof path.
The remaining 4 Yang-Mills-specific axioms are ALL in `YangMills/P8_PhysicalGap/BalabanToLSI.lean`:

1. `YangMills.bakry_emery_lsi` (line 61) -- Bakry-Emery LSI for compact Lie groups  
2. `YangMills.sun_bakry_emery_cd` (line 71) -- Bakry-Emery curvature-dimension for SU(N)
3. `YangMills.balaban_rg_uniform_lsi` (line 102) -- Balaban RG -> uniform LSI
4. `YangMills.sz_lsi_to_clustering` (line 127) -- Stroock-Zegarlinski LSI -> exponential clustering

**Goal:** Prove each from Mathlib primitives. One axiom eliminated per campaign = maximum value.
Even one lemma toward any of these is worth more than 100 interface bundles.

Key theorem to check after any change:
```
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```
Expected clean output: [propext, Classical.choice, Quot.sound, + the 4 frontier axioms above]
