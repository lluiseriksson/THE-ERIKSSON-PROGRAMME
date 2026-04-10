import YangMills.P8_PhysicalGap.VacuumBraFromProjectorInvariant

namespace YangMills
open ContinuousLinearMap MeasureTheory

section VacuumAdjointFixed
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C100-H1: right projector absorption from adjoint vacuum invariance
theorem projector_absorb_right_of_rankOneVacuumAdjointFixed
    (T P₀ : H →L[ℝ] H) (Ω : H)
    (hP₀ : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfixAdj : T.adjoint Ω = Ω) :
    P₀ * T = P₀ := by
  ext x
  simp only [mul_apply, hP₀, smulRight_apply, innerSL_apply]
  congr 1
  have key := ContinuousLinearMap.adjoint_inner_left T x Ω
  rw [hfixAdj] at key
  exact key.symm

end VacuumAdjointFixed

section FullChain
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C100-T1: ClayYangMills from ket + adjoint invariance (removes hPT)
theorem physicalStrong_of_projectedOpNormBound_rankOneVacuum_ketAdjointFixed
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω)
    (hfixAdj : T.adjoint Ω = Ω)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hPT := projector_absorb_right_of_rankOneVacuumAdjointFixed T P₀ Ω hP₀eq hfixAdj
  exact physicalStrong_of_projectedOpNormBound_rankOneVacuum_ketRightProjectorInvariant
    Ω hΩ hP₀eq hfix hPT m hm hproj hopnorm hdistP

end FullChain
end YangMills
