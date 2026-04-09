import YangMills.P8_PhysicalGap.ProjectedOpNormToComplementContraction

namespace YangMills
open ContinuousLinearMap MeasureTheory

section SelfAdjointVacuum
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C95-H1: T.adjoint = T → T Ω = Ω → T.adjoint Ω = Ω
theorem adjointFixed_of_selfAdjoint_fixed
    (T : H →L[ℝ] H) (Ω : H)
    (hselfAdj : T.adjoint = T)
    (hfix : T Ω = Ω) :
    T.adjoint Ω = Ω := by
  rw [hselfAdj]; exact hfix

-- C95-H2: P₀ * T = P₀ from self-adjoint T fixed on Ω
theorem rankOneProjector_absorb_right_of_selfAdjointFixed
    (T : H →L[ℝ] H) (Ω : H)
    (hselfAdj : T.adjoint = T)
    (hfix : T Ω = Ω) :
    ((innerSL ℝ Ω).smulRight Ω) * T = (innerSL ℝ Ω).smulRight Ω := by
  have hfixAdj : T.adjoint Ω = Ω :=
    adjointFixed_of_selfAdjoint_fixed T Ω hselfAdj hfix
  exact rankOneProjector_absorb_right_of_adjointFixed T Ω hfixAdj

end SelfAdjointVacuum

section FullChain
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C95-T1: ClayYangMills from self-adjoint T (single operators)
theorem physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_selfAdjoint
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω) (hselfAdj : T.adjoint = T)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hfixAdj : T.adjoint Ω = Ω :=
    adjointFixed_of_selfAdjoint_fixed T Ω hselfAdj hfix
  exact physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_biFixed
    Ω hΩ hP₀eq hfix hfixAdj m hm hproj hopnorm hdistP

end FullChain

end YangMills
