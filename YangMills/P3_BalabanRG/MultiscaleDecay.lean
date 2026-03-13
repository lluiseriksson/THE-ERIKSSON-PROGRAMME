import Mathlib
import YangMills.P3_BalabanRG.RGContraction

namespace YangMills

open MeasureTheory

/-! ## P3.3: Multiscale Decay -/

section MultiscaleDecay

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

def RGIteratedImprovement
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (m0 dm : ℝ) (n : ℕ) : Prop :=
  ∃ h : ConnectedCorrDecay μ plaquetteEnergy β F distP,
    m0 + n * dm ≤ h.m

def HasDecayIncrement
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) : Prop :=
  0 < dm ∧
  ∀ (h : ConnectedCorrDecay μ plaquetteEnergy β F distP),
    ∃ h' : ConnectedCorrDecay μ plaquetteEnergy β F distP,
      h.m + dm ≤ h'.m

theorem decayIncrement_implies_contraction
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm) :
    RGStepContraction μ plaquetteEnergy β F distP := by
  intro h
  obtain ⟨_, hstep⟩ := hinc
  obtain ⟨h', hh'⟩ := hstep h
  exact ⟨h', by linarith⟩

theorem rgIterated_improvement
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) (hdm : 0 < dm)
    (h0 : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm)
    (n : ℕ) :
    ∃ h : ConnectedCorrDecay μ plaquetteEnergy β F distP,
      h0.m + n * dm ≤ h.m := by
  induction n with
  | zero => exact ⟨h0, by simp⟩
  | succ n ih =>
    obtain ⟨hn, hhn⟩ := ih
    obtain ⟨_, hstep⟩ := hinc
    obtain ⟨h_next, hh_next⟩ := hstep hn
    refine ⟨h_next, ?_⟩
    have hs : h0.m + ((Nat.succ n : ℕ) : ℝ) * dm =
              h0.m + (n : ℝ) * dm + dm := by push_cast; ring
    rw [hs]; linarith

-- MultiscaleDecayBound: -(↑n * m') * dist
-- bound gives: -m * dist
-- package m' = hn.m/n, convert, congr 1, field_simp closes
theorem multiscaleDecay_of_iterated_contraction
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) (hdm : 0 < dm)
    (h0 : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm)
    (n : ℕ) (hn_pos : 0 < n) :
    MultiscaleDecayBound μ plaquetteEnergy β F distP n := by
  obtain ⟨hn, _⟩ := rgIterated_improvement μ plaquetteEnergy β F distP dm hdm h0 hinc n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  refine ⟨hn.C, hn.m / n, hn.hC, div_pos hn.hm hnR, ?_⟩
  intro N hN p q
  letI : NeZero N := hN
  have hb := hn.bound N p q
  convert hb using 2
  congr 1
  field_simp

-- hbound: C * exp(-↑n * m * dist)   [MultiscaleDecayBound uses -↑n * m]
-- goal:   C * exp(-(↑n * m) * dist)  [UniformWilsonDecay uses -(↑n*m)]
-- -↑n * m * dist = -(↑n * m) * dist by ring → use linarith via Real.exp_le_exp
theorem uniformWilsonDecay_of_multiscale
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (n : ℕ) (hn : 0 < n)
    (hms : MultiscaleDecayBound μ plaquetteEnergy β F distP n) :
    UniformWilsonDecay μ plaquetteEnergy β F distP := by
  obtain ⟨C, m, hC, hm, hbound⟩ := hms
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨C, (n : ℝ) * m, hC, mul_pos hnR hm, ?_⟩
  intro N hN p q
  letI : NeZero N := hN
  have hb := hbound N p q
  -- hb : |corr| ≤ C * exp(-↑n * m * dist)
  -- goal: |corr| ≤ C * exp(-(↑n * m) * dist)
  -- these are equal: -↑n * m * dist = -(↑n * m) * dist
  have heq : -↑n * m * distP N p q = -(↑n * m) * distP N p q := by ring
  rwa [heq] at hb

theorem multiscale_chain_uniformDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) (hdm : 0 < dm)
    (h0 : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm) :
    UniformWilsonDecay μ plaquetteEnergy β F distP :=
  h0.toUniformWilsonDecay

end MultiscaleDecay

section MultiscaleToUniform

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

theorem uniformDecay_of_connectedDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    UniformWilsonDecay μ plaquetteEnergy β F distP :=
  h.toUniformWilsonDecay

end MultiscaleToUniform

end YangMills
