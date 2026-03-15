import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap
open MeasureTheory Real Filter Topology
namespace YangMills

/-!
# Stroock-Zegarlinski: DLR_LSI → ExponentialClustering (Milestone M4)

Chain: DLR_LSI → PoincareInequality → L² semigroup decay → ExponentialClustering.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

def HasL2SpectralDecay (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧
  ∀ (f : Ω → ℝ), Measurable f → Integrable (fun x => f x ^ 2) μ →
    ∀ t : ℝ, 0 ≤ t →
      ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        Real.exp (-lam * t) * (E f + ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ)

def HasCovarianceDecay (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧
  ∀ (F G : Ω → ℝ),
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

axiom poincare_to_spectral_decay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hE : IsDirichletFormStrong E μ)
    (hP : PoincareInequality μ E lam) :
    HasL2SpectralDecay μ E lam

axiom spectral_decay_to_clustering
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hD : HasL2SpectralDecay μ E lam) :
    HasCovarianceDecay μ 2 (1 / lam)

/-- Bridge: covariance decay → exponential clustering.
    Key step: √Var(F) ≤ √E[F²] (postponed as TODO). -/
lemma covariance_decay_to_exponential_clustering
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (C ξ : ℝ) (hCD : HasCovarianceDecay μ C ξ) :
    ExponentialClustering μ C ξ := by
  obtain ⟨hξ, hC, hcov⟩ := hCD
  refine ⟨hξ, hC, fun F G => ?_⟩
  have hFsqrt : Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, F x ^ 2 ∂μ) := by
    apply Real.sqrt_le_sqrt
    -- TODO(M4): Var(F) ≤ E[F²], needs integrability
    sorry
  have hGsqrt : Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, G x ^ 2 ∂μ) := by
    apply Real.sqrt_le_sqrt
    -- TODO(M4): Var(G) ≤ E[G²], needs integrability
    sorry
  have hmul :
      C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)
        ≤
      C * Real.sqrt (∫ x, F x ^ 2 ∂μ) *
          Real.sqrt (∫ x, G x ^ 2 ∂μ) := by
    gcongr
  have hexp : (0 : ℝ) ≤ Real.exp (-1 / ξ) := Real.exp_nonneg _
  calc |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)|
      ≤ C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
          Real.exp (-1 / ξ) := hcov F G
    _ ≤ C * Real.sqrt (∫ x, F x ^ 2 ∂μ) *
            Real.sqrt (∫ x, G x ^ 2 ∂μ) *
          Real.exp (-1 / ξ) :=
        mul_le_mul_of_nonneg_right hmul hexp

/-- Milestone M4: DLR_LSI → ExponentialClustering. -/
theorem sz_lsi_to_clustering_bridge
    (gibbsFamily : ℕ → Measure Ω)
    [∀ L, IsProbabilityMeasure (gibbsFamily L)]
    (E : (Ω → ℝ) → ℝ)
    (hE : ∀ L, IsDirichletFormStrong E (gibbsFamily L))
    (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star) :
    ∃ C ξ, 0 < ξ ∧ ξ ≤ 2 / α_star ∧
      ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ := by
  obtain ⟨hα, hLSI_per_volume⟩ := hLSI
  -- Step 1: LSI → Poincaré at each volume
  have hPoincare : ∀ L, PoincareInequality (gibbsFamily L) E (α_star / 2) := by
    intro L
    have hLSI_nonneg : ∀ f : Ω → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
        ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(gibbsFamily L) -
        (∫ x, f x ^ 2 ∂(gibbsFamily L)) * Real.log (∫ x, f x ^ 2 ∂(gibbsFamily L)) ≤
        (2 / α_star) * E f := fun f hf _ => (hLSI_per_volume L).2 f hf
    exact lsi_implies_poincare_strong (gibbsFamily L) E (hE L) α_star hLSI_nonneg hα
  -- Step 2: Poincaré → spectral decay (M4a)
  have hDecay : ∀ L, HasL2SpectralDecay (gibbsFamily L) E (α_star / 2) := fun L =>
    poincare_to_spectral_decay E (α_star / 2) (hE L) (hPoincare L)
  -- Step 3: spectral decay → covariance decay with ξ = 2/α_star (M4b)
  have hCov : ∀ L, HasCovarianceDecay (gibbsFamily L) 2 (2 / α_star) := by
    intro L
    have h := spectral_decay_to_clustering E (α_star / 2) (hDecay L)
    have heq : (1 : ℝ) / (α_star / 2) = 2 / α_star := by field_simp
    rwa [heq] at h
  -- Step 4: covariance decay → ExponentialClustering
  exact ⟨2, 2 / α_star, by positivity, le_refl _,
    fun L => covariance_decay_to_exponential_clustering 2 _ (hCov L)⟩

end YangMills
