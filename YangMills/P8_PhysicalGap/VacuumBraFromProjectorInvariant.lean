import YangMills.P8_PhysicalGap.VacuumKetInvariant

namespace YangMills
open ContinuousLinearMap MeasureTheory

section VacuumBraFromProjector
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- C99-H1: bra invariance from rank-one projector right absorption
theorem braInvariant_of_rankOneProjector_absorb_right
    (T : H →L[ℝ] H) (Ω : H)
    (hΩ : ‖Ω‖ = 1)
    (hPT : ((innerSL ℝ Ω).smulRight Ω) * T = (innerSL ℝ Ω).smulRight Ω) :
    ∀ x : H, (innerSL ℝ Ω) (T x) = (innerSL ℝ Ω) x := by
  intro x
  have h : (((innerSL ℝ Ω).smulRight Ω) * T) x = ((innerSL ℝ Ω).smulRight Ω) x :=
    DFunLike.congr_fun hPT x
  simp only [mul_apply, smulRight_apply] at h
  rw [← sub_eq_zero]
  have hΩne : Ω ≠ 0 := by intro heq; simp [heq] at hΩ
  have key : ((innerSL ℝ Ω) (T x) - (innerSL ℝ Ω) x) • Ω = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp key).resolve_right hΩne

-- C99-H2: bra invariance from general projector right absorption
theorem braInvariant_of_projector_absorb_right_rankOneVacuum
    (T P₀ : H →L[ℝ] H) (Ω : H)
    (hP₀ : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hΩ : ‖Ω‖ = 1)
    (hPT : P₀ * T = P₀) :
    ∀ x : H, (innerSL ℝ Ω) (T x) = (innerSL ℝ Ω) x := by
  rw [hP₀] at hPT
  exact braInvariant_of_rankOneProjector_absorb_right T Ω hΩ hPT

end VacuumBraFromProjector

section FullChain
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- C99-T1: ClayYangMills from ket invariance + right projector invariance (no hbra)
theorem physicalStrong_of_projectedOpNormBound_rankOneVacuum_ketRightProjectorInvariant
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω)
    (hPT : P₀ * T = P₀)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hbra := braInvariant_of_projector_absorb_right_rankOneVacuum T P₀ Ω hP₀eq hΩ hPT
  exact physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_ketBraInvariant
    Ω hΩ hP₀eq hfix hbra m hm hproj hopnorm hdistP

end FullChain
end YangMills
