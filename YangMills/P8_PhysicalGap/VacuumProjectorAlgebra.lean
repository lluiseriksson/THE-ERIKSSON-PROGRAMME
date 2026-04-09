import Mathlib
import YangMills.P8_PhysicalGap.VacuumProjectorNorm

namespace YangMills
open ContinuousLinearMap MeasureTheory

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The rank-one projector onto a unit vector is idempotent. -/
theorem rankOneProjector_idem (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (innerSL ℝ Ω).smulRight Ω * (innerSL ℝ Ω).smulRight Ω =
    (innerSL ℝ Ω).smulRight Ω := by
  ext x
  simp only [mul_apply, smulRight_apply, map_smul, smul_smul]
  have hnn : (innerSL ℝ Ω) Ω = 1 := by
    have : (innerSL ℝ Ω) Ω = @inner ℝ H _ Ω Ω := rfl
    rw [this, real_inner_self_eq_norm_sq, hΩ, one_pow]
  rw [hnn, mul_one]

/-- If T fixes Ω, then T absorbs the rank-one projector from the left. -/
theorem rankOneProjector_absorb_left_of_fixed (T : H →L[ℝ] H) (Ω : H) (hfix : T Ω = Ω) :
    T * (innerSL ℝ Ω).smulRight Ω = (innerSL ℝ Ω).smulRight Ω := by
  ext x
  simp only [mul_apply, smulRight_apply, map_smul, hfix]

/-- If the adjoint of T fixes Ω, then T absorbs the rank-one projector from the right. -/
theorem rankOneProjector_absorb_right_of_adjointFixed (T : H →L[ℝ] H) (Ω : H)
    (hfixAdj : T.adjoint Ω = Ω) :
    (innerSL ℝ Ω).smulRight Ω * T = (innerSL ℝ Ω).smulRight Ω := by
  ext x
  simp only [mul_apply, smulRight_apply]
  congr 1
  have h1 : (innerSL ℝ Ω) (T x) = @inner ℝ H _ Ω (T x) := rfl
  have h2 : (innerSL ℝ Ω) x = @inner ℝ H _ Ω x := rfl
  rw [h1, h2, ← adjoint_inner_left, hfixAdj]

/-- Main wrapper: derive ClayYangMillsPhysicalStrong from bi-fixed rank-one vacuum hypothesis,
    automatically deriving the algebraic side-conditions hP₀_idem, hTP, hPT. -/
theorem physicalStrong_of_profiledComplementResidualContraction_rankOneVacuum_biFixed
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω)
    (hfixAdj : T.adjoint Ω = Ω)
    (m : ℝ) (hm : 0 < m)
    (hcomp : ∀ x : H, P₀ x = 0 → ‖(T - P₀) x‖ ≤ Real.exp (-m) * ‖x‖)
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hP₀_idem : P₀ * P₀ = P₀ := by
    rw [hP₀eq]; exact rankOneProjector_idem Ω hΩ
  have hTP : T * P₀ = P₀ := by
    rw [hP₀eq]; exact rankOneProjector_absorb_left_of_fixed T Ω hfix
  have hPT : P₀ * T = P₀ := by
    rw [hP₀eq]; exact rankOneProjector_absorb_right_of_adjointFixed T Ω hfixAdj
  exact physicalStrong_of_profiledComplementResidualContraction_rankOneVacuum
    Ω hΩ hP₀eq hP₀_idem hTP hPT m hm hcomp hopnorm hdistP

end YangMills
