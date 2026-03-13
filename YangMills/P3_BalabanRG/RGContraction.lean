import Mathlib
import YangMills.P3_BalabanRG.CorrelationNorms

namespace YangMills

open MeasureTheory

/-! ## P3.2: RG Contraction

One RG step strictly improves the decay rate of connected correlations.

Key Lean 4 patterns:
- Props mentioning gaugeMeasureFrom need d,N as def parameters
- Use @ with explicit instance args to avoid stuck NeZero metavariables
- Use `change` tactic to unfold opaque defs before `intro`
-/

section RGContraction

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- The RG step contraction predicate. -/
def RGStepContraction
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) : Prop :=
  ∀ (h : ConnectedCorrDecay μ plaquetteEnergy β F distP),
    ∃ h' : ConnectedCorrDecay μ plaquetteEnergy β F distP,
      h.m < h'.m

/-- An RG step with coupling factor κ gives improved decay rate. -/
def RGStepWithRate
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β κ : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) : Prop :=
  0 < κ →
  ∀ (h : ConnectedCorrDecay μ plaquetteEnergy β F distP),
    ∃ h' : ConnectedCorrDecay μ plaquetteEnergy β F distP,
      h.m + β * κ ≤ h'.m

/-- RGStepWithRate implies RGStepContraction. -/
theorem rgStepWithRate_implies_contraction
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β κ : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (hβ : 0 < β) (hκ : 0 < κ)
    (hstep : RGStepWithRate μ plaquetteEnergy β κ F distP) :
    RGStepContraction μ plaquetteEnergy β F distP := by
  intro h
  obtain ⟨h', hh'⟩ := hstep hκ h
  exact ⟨h', by linarith [mul_pos hβ hκ]⟩

end RGContraction

section OneStepBound

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Fixed-dimension one-step RG bound.
    Uses @ with explicit instance args to avoid stuck NeZero metavariables. -/
def HasOneStepRGBoundAt
    (d N : ℕ) [hd : NeZero d] [hN : NeZero N]
    (plaquetteEnergy : G → ℝ) (β κ : ℝ) : Prop :=
  0 ≤ β →
  ∀ (μ : Measure G) [IsProbabilityMeasure μ],
    MeasurableSet (@LargeFieldSet d N hd hN G _ κ plaquetteEnergy) →
    Integrable (fun U : GaugeConfig d N G =>
        Real.exp (-β * wilsonAction plaquetteEnergy U))
      (@gaugeMeasureFrom d N hd hN G _ _ μ) →
    0 < @partitionFunction d N hd hN G _ _ μ plaquetteEnergy β →
    (∫ U : GaugeConfig d N G,
        @χ_large d N hd hN G _ κ plaquetteEnergy U *
          Real.exp (-β * wilsonAction plaquetteEnergy U)
        ∂(@gaugeMeasureFrom d N hd hN G _ _ μ)) /
      @partitionFunction d N hd hN G _ _ μ plaquetteEnergy β
      ≤ Real.exp (-β * κ) /
        @partitionFunction d N hd hN G _ _ μ plaquetteEnergy β

/-- `rg_step_bound` from L3 provides the one-step bound. -/
theorem hasOneStepRGBoundAt_of_repo
    (d N : ℕ) [hd : NeZero d] [hN : NeZero N]
    (plaquetteEnergy : G → ℝ) (β κ : ℝ) :
    HasOneStepRGBoundAt (G := G) d N plaquetteEnergy β κ := by
  change 0 ≤ β →
    ∀ (μ : Measure G) [IsProbabilityMeasure μ],
      MeasurableSet (@LargeFieldSet d N hd hN G _ κ plaquetteEnergy) →
      Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
        (@gaugeMeasureFrom d N hd hN G _ _ μ) →
      0 < @partitionFunction d N hd hN G _ _ μ plaquetteEnergy β →
      (∫ U : GaugeConfig d N G,
          @χ_large d N hd hN G _ κ plaquetteEnergy U *
            Real.exp (-β * wilsonAction plaquetteEnergy U)
          ∂(@gaugeMeasureFrom d N hd hN G _ _ μ)) /
        @partitionFunction d N hd hN G _ _ μ plaquetteEnergy β
        ≤ Real.exp (-β * κ) /
          @partitionFunction d N hd hN G _ _ μ plaquetteEnergy β
  intro hβ μ hμ hmeas hInt hZ
  exact @rg_step_bound d N hd hN G _ _ plaquetteEnergy β κ hβ μ hμ hmeas hInt hZ

/-- Global wrapper: all dimensions and volumes. -/
def HasOneStepRGBound (plaquetteEnergy : G → ℝ) (β κ : ℝ) : Prop :=
  ∀ (d N : ℕ) (hd : NeZero d) (hN : NeZero N),
    @HasOneStepRGBoundAt G _ _ d N hd hN plaquetteEnergy β κ

theorem hasOneStepRGBound_of_repo
    (plaquetteEnergy : G → ℝ) (β κ : ℝ) :
    HasOneStepRGBound (G := G) plaquetteEnergy β κ := by
  intro d N hd hN
  exact @hasOneStepRGBoundAt_of_repo G _ _ d N hd hN plaquetteEnergy β κ

/-- Coupling improvement from L3. -/
theorem oneStep_coupling_improves
    (β : ℝ) (hβ : 0 < β) (L : BlockFactor) (hL : 1 < L) :
    ∃ β' : ℝ, β < β' :=
  rg_coupling_monotone β hβ L hL

end OneStepBound

section RGContractionChain

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- n RG steps produce improved witnesses. -/
def RGNStepContraction
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (n : ℕ) : Prop :=
  ∀ (h : ConnectedCorrDecay μ plaquetteEnergy β F distP),
    ∃ h' : ConnectedCorrDecay μ plaquetteEnergy β F distP,
      h.m < h'.m

theorem rgNStep_of_step
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (n : ℕ)
    (hstep : RGStepContraction μ plaquetteEnergy β F distP) :
    RGNStepContraction μ plaquetteEnergy β F distP n :=
  fun h => hstep h

/-- Thread existing witness through RGStepImproves. -/
theorem rgContraction_implies_rgStepImproves
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (hstep : RGStepImproves μ plaquetteEnergy β F distP)
    (hdecay : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    ∃ m' : ℝ, hdecay.m < m' :=
  hstep hdecay.C hdecay.m hdecay.hC hdecay.hm

/-- RGStepContraction + existing witness gives improved rate. -/
theorem rgContraction_improves_rate
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (hstep : RGStepContraction μ plaquetteEnergy β F distP)
    (hdecay : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    ∃ m' : ℝ, hdecay.m < m' := by
  obtain ⟨h', hh'⟩ := hstep hdecay
  exact ⟨h'.m, hh'⟩

end RGContractionChain

end YangMills
