import YangMills.P8_PhysicalGap.VacuumBraInvariant

namespace YangMills
open ContinuousLinearMap MeasureTheory

section VacuumKetInvariant
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- C98-H1: rank-one projector absorbs T from left via ket invariance
theorem rankOneProjector_absorb_left_of_ketInvariant
    (T : H →L[ℝ] H) (Ω : H)
    (hfix : T Ω = Ω) :
    T * ((innerSL ℝ Ω).smulRight Ω) = (innerSL ℝ Ω).smulRight Ω := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smulRight_apply,
             map_smul, hfix]

-- C98-H2: general projector absorbs T from left via ket invariance
theorem projector_absorb_left_of_rankOneVacuumKetInvariant
    (T P₀ : H →L[ℝ] H) (Ω : H)
    (hP₀ : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω) :
    T * P₀ = P₀ := by
  rw [hP₀]
  exact rankOneProjector_absorb_left_of_ketInvariant T Ω hfix

end VacuumKetInvariant

section FullChain
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C98-T1: ClayYangMills from ket+bra invariance (derives T * P₀ = P₀ internally)
theorem physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_ketBraInvariant
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω)
    (hbra : ∀ x : H, (innerSL ℝ Ω) (T x) = (innerSL ℝ Ω) x)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hTP : T * P₀ = P₀ :=
    projector_absorb_left_of_rankOneVacuumKetInvariant T P₀ Ω hP₀eq hfix
  exact physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_braInvariant
    Ω hΩ hP₀eq hTP hbra m hm hproj hopnorm hdistP

end FullChain
end YangMills
