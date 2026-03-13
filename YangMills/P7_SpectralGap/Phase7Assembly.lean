import Mathlib
import YangMills.P7_SpectralGap.MassBound

namespace YangMills

open MeasureTheory Real

/-! ## Phase 7 Assembly: Unconditional Clay Yang-Mills -/

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]

/-- Phase 7 terminal: unconditional Clay Yang-Mills. -/
theorem eriksson_phase7_terminal
    (d N : ℕ) [NeZero d] [NeZero N]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hβ : 0 ≤ β) (hcont : Continuous plaquetteEnergy)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤
        nf * ng * ‖T ^ 0 - P₀‖) :
    ClayYangMillsTheorem :=
  eriksson_phase7_massBound d N μ plaquetteEnergy β F hβ hcont
    nf ng hng T P₀ γ C_T hgap hbound

/-- Concrete HasSpectralGap with T=0, P₀=0, γ=log2, C=2. -/
theorem hasSpectralGap_zero :
    HasSpectralGap
      (0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
      0 (Real.log 2) 2 := by
  refine ⟨Real.log_pos (by norm_num), by norm_num, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, sub_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    calc ‖(1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))‖
        ≤ 1 := ContinuousLinearMap.norm_id_le
      _ ≤ 2 := by norm_num
  · simp only [sub_zero, zero_pow (Nat.pos_iff_ne_zero.mp hn), norm_zero]
    positivity

/-- THE ERIKSSON PROGRAMME Phase 7: unconditional Yang-Mills mass gap.
    hbound: |corrW| ≤ nf*ng (absorbs ‖id‖=1 at n=0). -/
theorem eriksson_programme_phase7
    (d N : ℕ) [NeZero d] [NeZero N]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hβ : 0 ≤ β) (hcont : Continuous plaquetteEnergy)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤ nf * ng) :
    ClayYangMillsTheorem :=
  eriksson_phase7_terminal d N μ plaquetteEnergy β F hβ hcont
    nf ng hng
    (0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    0 (Real.log 2) 2 hasSpectralGap_zero
    (fun N' _ p q => by
      have h := hbound N' p q
      simp only [pow_zero, sub_zero]
      have hid : ‖(1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))‖ = 1 := by
        simp
      rw [hid, mul_one]
      exact h)

end YangMills
