import YangMills.P8_PhysicalGap.ComplementContractionToResidual

/-!
## C94: ProjectedOpNormToComplementContraction

Derives pointwise complement contraction from the weaker single
operator-norm bound on T ∘ (1 - P₀). This is a genuine live-path
weakening: C93 needed ∀ x, P₀ x = 0 → ‖T x‖ ≤ exp(-m)‖x‖;
C94 replaces it with the single bound ‖T * (1 - P₀)‖ ≤ exp(-m).
-/

namespace YangMills

open ContinuousLinearMap MeasureTheory

section ProjectedOpNorm

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- C94-H1: On ker P₀, the complement projector (1 - P₀) acts as
    the identity. -/
theorem complement_projector_apply_eq_self_of_kernel
    (P₀ : H →L[ℝ] H)
    {x : H} (hx : P₀ x = 0) :
    ((1 : H →L[ℝ] H) - P₀) x = x := by
  simp [ContinuousLinearMap.sub_apply, hx]

/-- C94-H2: A single operator-norm bound ‖T * (1 - P₀)‖ ≤ exp(-m)
    implies pointwise complement contraction
    ∀ x, P₀ x = 0 → ‖T x‖ ≤ exp(-m) * ‖x‖. -/
theorem complementContraction_of_projectedOpNormBound
    (T P₀ : H →L[ℝ] H)
    (m : ℝ)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m)) :
    ∀ X : H, P₀ X = 0 → ‖T X‖ ≤ Real.exp (-m) * ‖X‖ := by
  intro X hX
  have h1 : ((1 : H →L[ℝ] H) - P₀) X = X :=
    complement_projector_apply_eq_self_of_kernel P₀ hX
  have h3 : (T * ((1 : H →L[ℝ] H) - P₀)) X = T X := by
    simp [ContinuousLinearMap.mul_apply, h1]
  have h2 : ‖(T * ((1 : H →L[ℝ] H) - P₀)) X‖ ≤
      ‖T * ((1 : H →L[ℝ] H) - P₀)‖ * ‖X‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [h3] at h2
  exact le_trans h2 (mul_le_mul_of_nonneg_right hproj (norm_nonneg _))

end ProjectedOpNorm

section FullChain

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- C94-T1: ClayYangMills from the projected-operator-norm assumption.
    Wraps C93-T1 by first applying H2. -/
theorem physicalStrong_of_profiledProjectedOpNormBound_rankOneVacuum_biFixed
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω)
    (hfixAdj : T.adjoint Ω = Ω)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hcompT : ∀ x : H, P₀ x = 0 → ‖T x‖ ≤ Real.exp (-m) * ‖x‖ :=
    complementContraction_of_projectedOpNormBound T P₀ m hproj
  exact physicalStrong_of_profiledComplementContraction_rankOneVacuum_biFixed
    Ω hΩ hP₀eq hfix hfixAdj m hm hcompT hopnorm hdistP

end FullChain

end YangMills
