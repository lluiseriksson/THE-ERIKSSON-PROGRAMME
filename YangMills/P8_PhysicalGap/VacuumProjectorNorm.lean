import Mathlib
import YangMills.P8_PhysicalGap.ComplementResidualContraction

namespace YangMills
open ContinuousLinearMap MeasureTheory

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem one_sub_rankOneProjector_apply_norm_le (Ω x : H) (hΩ : ‖Ω‖ = 1) :
    ‖x - @inner ℝ H _ Ω x • Ω‖ ≤ ‖x‖ := by
  have h1 : @inner ℝ H _ x (@inner ℝ H _ Ω x • Ω) = @inner ℝ H _ Ω x ^ 2 := by
    rw [inner_smul_right, real_inner_comm x Ω, sq]
  have h2 : ‖@inner ℝ H _ Ω x • Ω‖ ^ 2 = @inner ℝ H _ Ω x ^ 2 := by
    rw [norm_smul, hΩ, mul_one, Real.norm_eq_abs, sq_abs]
  have key : ‖x - @inner ℝ H _ Ω x • Ω‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h := norm_sub_sq_real x (@inner ℝ H _ Ω x • Ω)
    rw [h1, h2] at h
    linarith [sq_nonneg (@inner ℝ H _ Ω x)]
  rw [← Real.sqrt_sq (norm_nonneg (x - @inner ℝ H _ Ω x • Ω)),
      ← Real.sqrt_sq (norm_nonneg x)]
  exact Real.sqrt_le_sqrt key

theorem norm_one_sub_rankOneProjector_le_one (Ω : H) (hΩ : ‖Ω‖ = 1) :
    ‖(1 : H →L[ℝ] H) - (innerSL ℝ Ω).smulRight Ω‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ one_pos.le (fun x => by
    simp only [sub_apply, one_apply, smulRight_apply, innerSL_apply_apply]
    rw [one_mul]
    exact one_sub_rankOneProjector_apply_norm_le Ω x hΩ)

theorem physicalStrong_of_profiledComplementResidualContraction_rankOneVacuum
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hP₀_idem : P₀ * P₀ = P₀) (hTP : T * P₀ = P₀) (hPT : P₀ * T = P₀)
    (m : ℝ) (hm : 0 < m)
    (hcomp : ∀ x : H, P₀ x = 0 → ‖(T - P₀) x‖ ≤ Real.exp (-m) * ‖x‖)
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hPnorm : ‖(1 : H →L[ℝ] H) - P₀‖ ≤ 1 := by
    simpa [hP₀eq] using norm_one_sub_rankOneProjector_le_one Ω hΩ
  exact physicalStrong_of_profiledComplementResidualContraction
    hP₀_idem hTP hPT hPnorm m hm hcomp hopnorm hdistP

end YangMills
