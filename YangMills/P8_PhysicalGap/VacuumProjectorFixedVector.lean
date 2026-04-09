import YangMills.P8_PhysicalGap.SelfAdjointVacuum

namespace YangMills
open ContinuousLinearMap MeasureTheory

section VacuumProjectorFixedVector
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- C96-H1: P₀ Ω = Ω when Ω is the rank-one projector vacuum
theorem rankOneProjector_apply_self
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    ((innerSL ℝ Ω).smulRight Ω) Ω = Ω := by
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply]
  rw [real_inner_self_eq_norm_sq, hΩ]
  simp

-- C96-H2: T Ω = Ω from T * P₀ = P₀
theorem fixed_of_projector_absorb_left_rankOneVacuum
    (T P₀ : H →L[ℝ] H) (Ω : H)
    (hP₀ : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hΩ : ‖Ω‖ = 1)
    (hTP : T * P₀ = P₀) :
    T Ω = Ω := by
  have hP₀Ω : P₀ Ω = Ω := by
    rw [hP₀]; exact rankOneProjector_apply_self Ω hΩ
  have h := congr_fun (congr_arg DFunLike.coe hTP) Ω
  simp only [ContinuousLinearMap.mul_apply] at h
  rw [hP₀Ω] at h
  exact h

end VacuumProjectorFixedVector

section FullChain
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C96-T1: ClayYangMills from T * P₀ = P₀ and self-adjoint T
theorem physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_selfAdjoint_projectorInvariant
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hTP : T * P₀ = P₀) (hselfAdj : T.adjoint = T)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hfix : T Ω = Ω :=
    fixed_of_projector_absorb_left_rankOneVacuum T P₀ Ω hP₀eq hΩ hTP
  exact physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_selfAdjoint
    Ω hΩ hP₀eq hfix hselfAdj m hm hproj hopnorm hdistP

end FullChain

end YangMills
