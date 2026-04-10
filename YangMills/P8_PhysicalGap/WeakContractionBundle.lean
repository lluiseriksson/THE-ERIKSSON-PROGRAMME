import YangMills.P8_PhysicalGap.PhysicalContractionBundle

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
         {d : ℕ} [NeZero d]

open MeasureTheory

/-- HasWeakNormContraction: operator norm contraction without the strict positivity
    condition `0 < ‖T - P₀‖`. Covers the degenerate case T = P₀ where all
    Wilson correlators vanish and the mass gap holds trivially. -/
def HasWeakNormContraction (T P₀ : H →L[ℝ] H) : Prop :=
  P₀ * P₀ = P₀ ∧ T * P₀ = P₀ ∧ P₀ * T = P₀ ∧ ‖T - P₀‖ < 1

/-- When T = P₀, HasSpectralGap holds trivially with γ = 1:
    T^(n+1) = P₀ for all n (by P₀² = P₀), so T^(n+1) - P₀ = 0. -/
private lemma hasSpectralGap_of_T_eq_P₀ {T P₀ : H →L[ℝ] H}
    (heq : T = P₀) (hidem : P₀ * P₀ = P₀) :
    HasSpectralGap T P₀ 1 (‖(1 : H →L[ℝ] H) - P₀‖ + 1) := by
  refine ⟨one_pos, by linarith [norm_nonneg ((1 : H →L[ℝ] H) - P₀)], fun n => ?_⟩
  cases n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    linarith [norm_nonneg ((1 : H →L[ℝ] H) - P₀)]
  | succ n =>
    have hpow : T ^ (n + 1) = P₀ := by
      induction n with
      | zero => rw [pow_one, heq]
      | succ k ih => rw [pow_succ, ih, heq, hidem]
    rw [hpow, sub_self, norm_zero]
    positivity

/-- C108: ClayYangMillsPhysicalStrong from PhysicalFeynmanKacFormula +
    HasWeakNormContraction (4 conditions, dropping `0 < ‖T - P₀‖`).
    Case split: T = P₀ (trivial gap via idempotency) or T ≠ P₀ (use C107). -/
theorem physicalStrong_of_physicalFormula_weakNormContraction
    {μ : MeasureTheory.Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (hpFK : PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hwc : HasWeakNormContraction T P₀) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  rcases (norm_nonneg (T - P₀)).eq_or_lt with h0 | hpos
  · have heq : T = P₀ := sub_eq_zero.mp (norm_eq_zero.mp h0.symm)
    exact physicalStrong_of_physicalFormula_spectralGap hpFK
      (hasSpectralGap_of_T_eq_P₀ heq hwc.1)
  · exact physicalStrong_of_physicalFormula_normContraction hpFK
      ⟨hwc.1, hwc.2.1, hwc.2.2.1, hpos, hwc.2.2.2⟩

/-- WeakPhysicalContractionBundle: bundles PhysicalFeynmanKacFormula with
    HasWeakNormContraction (4-condition variant, dropping `0 < ‖T - P₀‖`). -/
def WeakPhysicalContractionBundle
    (μ : MeasureTheory.Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧
  HasWeakNormContraction T P₀

theorem physicalStrong_of_weakPhysicalContractionBundle
    {μ : MeasureTheory.Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (h : WeakPhysicalContractionBundle μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_physicalFormula_weakNormContraction h.1 h.2

end YangMills
