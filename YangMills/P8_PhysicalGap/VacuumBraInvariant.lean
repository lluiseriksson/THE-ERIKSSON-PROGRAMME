import YangMills.P8_PhysicalGap.VacuumProjectorFixedVector

namespace YangMills
open ContinuousLinearMap MeasureTheory

section VacuumBraInvariant
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- C97-H1: rank-one projector absorbs T from right via bra invariance
theorem rankOneProjector_absorb_right_of_braInvariant
    (T : H →L[ℝ] H) (Ω : H)
    (hbra : ∀ x : H, (innerSL ℝ Ω) (T x) = (innerSL ℝ Ω) x) :
    ((innerSL ℝ Ω).smulRight Ω) * T = (innerSL ℝ Ω).smulRight Ω := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smulRight_apply]
  rw [hbra x]

-- C97-H2: general projector absorbs T from right via bra invariance
theorem projector_absorb_right_of_rankOneVacuumBraInvariant
    (T P₀ : H →L[ℝ] H) (Ω : H)
    (hP₀ : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hbra : ∀ x : H, (innerSL ℝ Ω) (T x) = (innerSL ℝ Ω) x) :
    P₀ * T = P₀ := by
  rw [hP₀]
  exact rankOneProjector_absorb_right_of_braInvariant T Ω hbra

end VacuumBraInvariant

section FullChain
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C97-T1: ClayYangMills from bra invariance (removes self-adjointness hypothesis)
theorem physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_braInvariant
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hTP : T * P₀ = P₀)
    (hbra : ∀ x : H, (innerSL ℝ Ω) (T x) = (innerSL ℝ Ω) x)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hfix : T Ω = Ω :=
    fixed_of_projector_absorb_left_rankOneVacuum T P₀ Ω hP₀eq hΩ hTP
  have hfixAdj : T.adjoint Ω = Ω := by
    have key : ∀ x : H, @inner ℝ H _ (T.adjoint Ω - Ω) x = 0 := fun x => by
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
      have hb := hbra x
      simp only [innerSL_apply] at hb
      linarith
    have h2 : T.adjoint Ω - Ω = 0 :=
      inner_self_eq_zero.mp (key (T.adjoint Ω - Ω))
    exact sub_eq_zero.mp h2
  exact physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_biFixed
    Ω hΩ hP₀eq hfix hfixAdj m hm hproj hopnorm hdistP

end FullChain
end YangMills
