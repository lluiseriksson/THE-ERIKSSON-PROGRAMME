import Mathlib
import YangMills.P3_BalabanRG.Phase3Assembly
import YangMills.P5_KPDecay.KPHypotheses

namespace YangMills

open MeasureTheory Real

/-! ## F5.2: Balaban Bootstrap — RG iteration → UniformWilsonDecay

Key insight: build ConnectedCorrDecay seed directly via ⟨C, m, hC, hm, hKP⟩
rather than via phase5_kp_sufficient, to avoid [NeZero N] elaboration issues.
-/

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Seed + RG increment → UniformWilsonDecay. -/
theorem balabanBootstrap_uniformDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) (hdm : 0 < dm)
    (h0 : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm) :
    UniformWilsonDecay μ plaquetteEnergy β F distP :=
  uniformWilsonDecay_of_multiscale μ plaquetteEnergy β F distP 1 one_pos
    (multiscaleDecay_of_iterated_contraction μ plaquetteEnergy β F distP dm hdm h0 hinc 1 one_pos)

/-- Seed + increment → ConnectedCorrDecay (Type → noncomputable def). -/
noncomputable def balabanBootstrap_connectedCorrDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) (hdm : 0 < dm)
    (h0 : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP := h0

/-- After n RG steps, rate ≥ h0.m + n * dm. -/
theorem balabanBootstrap_improvedRate
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) (hdm : 0 < dm)
    (h0 : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm)
    (n : ℕ) :
    ∃ hn : ConnectedCorrDecay μ plaquetteEnergy β F distP,
      h0.m + (n : ℝ) * dm ≤ hn.m :=
  rgIterated_improvement μ plaquetteEnergy β F distP dm hdm h0 hinc n

/-- KP seed + increment → UniformWilsonDecay.
    Direct constructor ⟨C, m, hC, hm, hKP⟩ avoids [NeZero N] elaboration issues. -/
theorem phase5_bootstrap_uniformDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m dm : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hdm : 0 < dm)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q))
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm) :
    UniformWilsonDecay μ plaquetteEnergy β F distP :=
  balabanBootstrap_uniformDecay μ plaquetteEnergy β F distP dm hdm
    ⟨C, m, hC, hm, hKP⟩ hinc

/-- F5.2 terminal: KP + RG → improved rate m + n*dm. -/
theorem phase5_bootstrap_improvedDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m dm : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hdm : 0 < dm)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q))
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm)
    (n : ℕ) :
    ∃ hn : ConnectedCorrDecay μ plaquetteEnergy β F distP,
      m + (n : ℝ) * dm ≤ hn.m := by
  obtain ⟨hn, hrate⟩ := rgIterated_improvement μ plaquetteEnergy β F distP dm hdm
    ⟨C, m, hC, hm, hKP⟩ hinc n
  exact ⟨hn, hrate⟩

end YangMills
