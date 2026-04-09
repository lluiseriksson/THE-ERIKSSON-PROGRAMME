import Mathlib
import YangMills.P8_PhysicalGap.PointwiseResidualContraction
import YangMills.P8_PhysicalGap.ProfiledSpectralGap

namespace YangMills
open ContinuousLinearMap Real MeasureTheory

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem opNormBound_of_complementResidualContraction
    (T P₀ : H →L[ℝ] H)
    (hP₀_idem : P₀ * P₀ = P₀)
    (hTP : T * P₀ = P₀)
    (m : ℝ)
    (hcomp : ∀ x : H, P₀ x = 0 → ‖(T - P₀) x‖ ≤ Real.exp (-m) * ‖x‖) :
    ‖T - P₀‖ ≤ Real.exp (-m) * ‖(1 : H →L[ℝ] H) - P₀‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
    (fun x => by
      have hzero : (T - P₀) * P₀ = 0 := by
        rw [sub_mul, hTP, hP₀_idem, sub_self]
      have hTP_zero : (T - P₀) (P₀ x) = 0 := by
        have h := DFunLike.congr_fun hzero x
        simp only [mul_apply, zero_apply] at h; exact h
      have hPQ_zero : P₀ * (1 - P₀) = 0 := by
        rw [mul_sub, mul_one, hP₀_idem, sub_self]
      have hPy : P₀ ((1 - P₀) x) = 0 := by
        have h := DFunLike.congr_fun hPQ_zero x
        simp only [mul_apply, zero_apply] at h; exact h
      have hrewrite : (T - P₀) x = (T - P₀) ((1 - P₀) x) := by
        have hdecomp : x = P₀ x + (1 - P₀) x := by
          rw [sub_apply, one_apply]; abel
        conv_lhs => rw [hdecomp]
        rw [map_add, hTP_zero, zero_add]
      calc ‖(T - P₀) x‖
          = ‖(T - P₀) ((1 - P₀) x)‖ := by rw [hrewrite]
        _ ≤ Real.exp (-m) * ‖(1 - P₀) x‖ := hcomp _ hPy
        _ ≤ Real.exp (-m) * (‖(1 : H →L[ℝ] H) - P₀‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (le_opNorm _ _) (Real.exp_nonneg _)
        _ = Real.exp (-m) * ‖(1 : H →L[ℝ] H) - P₀‖ * ‖x‖ := by ring)

theorem physicalStrong_of_profiledComplementResidualContraction
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (hP₀_idem : P₀ * P₀ = P₀) (hTP : T * P₀ = P₀) (hPT : P₀ * T = P₀)
    (hPnorm : ‖(1 : H →L[ℝ] H) - P₀‖ ≤ 1)
    (m : ℝ) (hm : 0 < m)
    (hcomp : ∀ x : H, P₀ x = 0 → ‖(T - P₀) x‖ ≤ Real.exp (-m) * ‖x‖)
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_profiledExpNormBound hP₀_idem hTP hPT m hm
    ((opNormBound_of_complementResidualContraction T P₀ hP₀_idem hTP m hcomp).trans
      (mul_le_of_le_one_right (Real.exp_nonneg _) hPnorm))
    hopnorm hdistP

end YangMills
