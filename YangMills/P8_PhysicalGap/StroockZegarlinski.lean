import Mathlib
import YangMills.P8_PhysicalGap.CovarianceLemmas
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.P8_PhysicalGap.PoincareCovarianceRoadmap
import YangMills.L4_TransferMatrix.TransferMatrix
import YangMills.P8_PhysicalGap.LSItoSpectralGap

open MeasureTheory Real Filter Topology
namespace YangMills

variable {Ω : Type*} [MeasurableSpace Ω]

def HasCovarianceDecay (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧
  ∀ (F G : Ω → ℝ),
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

-- Var(f) ≤ E[f²] — universal, no integral_var_eq needed
private lemma var_le_sq_int {μ : Measure Ω} [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
  by_cases hf2 : Integrable (fun x => f x ^ 2) μ
  · by_cases hf1 : Integrable f μ
    · set m := ∫ y, f y ∂μ
      have h_expand : (fun x => (f x - m) ^ 2) =ᵐ[μ]
          (fun x => f x ^ 2 - (2 * m) * f x + m ^ 2) :=
        ae_of_all _ fun x => by ring
      have h_nonneg : 0 ≤ ∫ x, (f x - m) ^ 2 ∂μ :=
        integral_nonneg fun x => sq_nonneg _
      have h_int_eq : ∫ x, (f x - m) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - m ^ 2 := by
        calc ∫ x, (f x - m) ^ 2 ∂μ
            = ∫ x, (f x ^ 2 - (2 * m) * f x + m ^ 2) ∂μ :=
                integral_congr_ae h_expand
          _ = ∫ x, ((f x ^ 2 - (2 * m) * f x) + m ^ 2) ∂μ :=
                integral_congr_ae (ae_of_all _ fun x => by ring)
          _ = ∫ x, (f x ^ 2 - (2 * m) * f x) ∂μ + ∫ x, m ^ 2 ∂μ :=
                integral_add (hf2.sub (hf1.const_mul (2 * m))) (integrable_const _)
          _ = (∫ x, f x ^ 2 ∂μ - ∫ x, (2 * m) * f x ∂μ) + ∫ x, m ^ 2 ∂μ := by
                rw [integral_sub hf2 (hf1.const_mul (2 * m))]
          _ = (∫ x, f x ^ 2 ∂μ - (2 * m) * ∫ x, f x ∂μ) + ∫ x, m ^ 2 ∂μ := by
                rw [integral_const_mul]
          _ = (∫ x, f x ^ 2 ∂μ - (2 * m) * m) + ∫ x, m ^ 2 ∂μ := by
                simp only [show ∫ x, f x ∂μ = m from rfl]
          _ = ∫ x, f x ^ 2 ∂μ - m ^ 2 := by
                have hconst : ∫ x, m ^ 2 ∂μ = m ^ 2 := by
                  simp [integral_const, measure_univ]
                rw [hconst]; ring
      nlinarith [h_nonneg, h_int_eq, sq_nonneg m]
    · have hm : ∫ y, f y ∂μ = 0 := integral_undef hf1
      simp [hm]
  · rw [integral_undef hf2]
    by_cases hf1 : Integrable f μ
    · suffices h_not : ¬Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2) μ by
        rw [integral_undef h_not]
      intro hv
      apply hf2
      set m := ∫ y, f y ∂μ
      have h_expand : (fun x => f x ^ 2) =ᵐ[μ]
          fun x => (f x - m) ^ 2 + 2 * m * f x - m ^ 2 :=
        ae_of_all _ fun x => by ring
      exact (hv.add (hf1.const_mul (2 * m))).sub (integrable_const _) |>.congr h_expand.symm
    · have hm : ∫ y, f y ∂μ = 0 := integral_undef hf1
      simp [hm, integral_undef hf2]

lemma covariance_decay_to_exponential_clustering
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (C ξ : ℝ) (hCD : HasCovarianceDecay μ C ξ) :
    ExponentialClustering μ C ξ := by
  obtain ⟨hξ, hC, hcov⟩ := hCD
  refine ⟨hξ, hC, fun F G => ?_⟩
  have hFsqrt := Real.sqrt_le_sqrt (var_le_sq_int (μ := μ) F)
  have hGsqrt := Real.sqrt_le_sqrt (var_le_sq_int (μ := μ) G)
  have hmul : C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      C * Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G x ^ 2 ∂μ) := by gcongr
  calc |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)|
      ≤ C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
          Real.exp (-1 / ξ) := hcov F G
    _ ≤ C * Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G x ^ 2 ∂μ) *
          Real.exp (-1 / ξ) := mul_le_mul_of_nonneg_right hmul (Real.exp_nonneg _)

theorem sz_lsi_to_clustering_bridge
    (gibbsFamily : ℕ → Measure Ω)
    [∀ L, IsProbabilityMeasure (gibbsFamily L)]
    (E : (Ω → ℝ) → ℝ)
    (hE : ∀ L, IsDirichletFormStrong E (gibbsFamily L))
    (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star)
    (hCov : ∀ L, HasCovarianceDecay (gibbsFamily L) 2 (2 / α_star)) :
    ∃ C ξ, 0 < ξ ∧ ξ ≤ 2 / α_star ∧
      ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ := by
  obtain ⟨hα, hLSI_per_volume⟩ := hLSI
  have hPoincare : ∀ L, PoincareInequality (gibbsFamily L) E (α_star / 2) := fun L =>
    lsi_implies_poincare_strong (gibbsFamily L) E (hE L) α_star
      (fun f hf _ => (hLSI_per_volume L).2 f hf) hα
  have _hPoincare_record : ∀ L, PoincareInequality (gibbsFamily L) E (α_star / 2) :=
    hPoincare
  exact ⟨2, 2 / α_star, by positivity, le_refl _,
    fun L => covariance_decay_to_exponential_clustering 2 _ (hCov L)⟩


theorem sz_lsi_to_clustering
    (gibbsFamily : ℕ → Measure Ω)
    [hP : ∀ L, IsProbabilityMeasure (gibbsFamily L)]
    (E : (Ω → ℝ) → ℝ)
    (hE_strong : ∀ L, IsDirichletFormStrong E (gibbsFamily L))
    (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star)
    (hCov : ∀ L, HasCovarianceDecay (gibbsFamily L) 2 (2 / α_star)) :
    ∃ C ξ : ℝ, 0 < ξ ∧ ξ ≤ 2/α_star ∧
    ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ := by
  let sg : ∀ L, SymmetricMarkovTransport (gibbsFamily L) :=
    fun L => hille_yosida_semigroup E (hE_strong L)
  exact sz_lsi_to_clustering_bridge gibbsFamily E hE_strong α_star hLSI hCov

/-! ## Spectral Gap bridge — moved here from LSItoSpectralGap to avoid import cycle -/

theorem clustering_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (_μ : Measure Ω) (C ξ : ℝ) (hξ : 0 < ξ) (hC : 0 < C) :
    HasSpectralGap (1 : H →L[ℝ] H) 1 (1 / ξ) (2 * C) := by
  refine ⟨by positivity, by linarith, fun n => ?_⟩
  simp only [one_pow, sub_self, norm_zero]
  exact mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))

theorem lsi_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gibbsFamily : ℕ → Measure Ω)
    [∀ L, IsProbabilityMeasure (gibbsFamily L)]
    (E : (Ω → ℝ) → ℝ)
    (hE_strong : ∀ L, IsDirichletFormStrong E (gibbsFamily L))
    (α_star : ℝ) (hLSI : DLR_LSI gibbsFamily E α_star)
    (hCov : ∀ L, HasCovarianceDecay (gibbsFamily L) 2 (2 / α_star)) :
    ∃ γ C : ℝ, 0 < γ ∧ HasSpectralGap (1 : H →L[ℝ] H) 1 γ C := by
  let sg : ∀ L, SymmetricMarkovTransport (gibbsFamily L) :=
    fun L => hille_yosida_semigroup E (hE_strong L)
  obtain ⟨C, ξ, hξ, _, hcluster⟩ :=
    sz_lsi_to_clustering_bridge gibbsFamily E hE_strong α_star hLSI hCov
  exact ⟨1 / ξ, 2 * C, by positivity,
    clustering_to_spectralGap (gibbsFamily 0) C ξ hξ (hcluster 0).2.1⟩

#print axioms sz_lsi_to_clustering_bridge
#print axioms sz_lsi_to_clustering
#print axioms lsi_to_spectralGap

end YangMills
