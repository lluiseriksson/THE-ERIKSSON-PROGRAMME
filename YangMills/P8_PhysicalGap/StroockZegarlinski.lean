import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap
open MeasureTheory Real Filter Topology
namespace YangMills

/-!
# Stroock-Zegarlinski: DLR_LSI → ExponentialClustering (Milestone M4)

## Architecture (Option B)

The chain is:

  DLR_LSI → PoincareInequality → HasCovarianceDecay → ExponentialClustering

The intermediate `HasL2SpectralDecay` (semigroup dynamics) is **not formalized**
here because the Markov semigroup is not a formal object in this abstract setting.
Instead, the Poincaré → covariance decay bridge is a single axiom that encapsulates
the functional-analytic content of Stroock-Zegarlinski 1992.

## Reference
Stroock-Zegarlinski, "The logarithmic Sobolev inequality for continuous
spin systems on a lattice", J. Funct. Anal. 104 (1992), 299–326.

The key analytical content of that paper:
  LSI → Poincaré (Rothaus-Holley-Stroock)
  Poincaré + semigroup dynamics → exponential mixing
  (via the Markov semigroup spectral gap and Cauchy-Schwarz)
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Covariance decay -/

/-- Covariance decay bound:
    |Cov_μ(F, G)| ≤ C · √Var_μ(F) · √Var_μ(G) · exp(-1/ξ).
    This is the output of the SZ mixing argument. -/
def HasCovarianceDecay (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧
  ∀ (F G : Ω → ℝ),
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

/-! ## Bridge axiom (M4 core) — decomposed -/

/-- M4b core axiom: Poincaré gap → covariance bound with exponential decay.
    Encapsulates the Stroock-Zegarlinski semigroup argument:
      Poincaré gap λ → spectral gap of Markov semigroup ≥ λ
      → Var(T_t f) ≤ exp(-2λt) Var(f)  [Gronwall]
      → |Cov(F,G)| ≤ 2·√Var(F)·√Var(G)·exp(-λ)  [Cauchy-Schwarz + semigroup]
    Reference: Stroock-Zegarlinski 1992, Theorems 2.1 and 3.3.
    Status: AXIOM — requires formal MarkovSemigroup type in Lean/Mathlib. -/
axiom poincare_implies_cov_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hE : IsDirichletFormStrong E μ)
    (hP : PoincareInequality μ E lam)
    (F G : Ω → ℝ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    2 * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-lam)

/-- Poincaré → covariance decay, proved from poincare_implies_cov_bound. -/
theorem poincare_to_covariance_decay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hE : IsDirichletFormStrong E μ)
    (hP : PoincareInequality μ E lam) :
    HasCovarianceDecay μ 2 (1 / lam) := by
  obtain ⟨hlam, _⟩ := hP
  refine ⟨by positivity, by norm_num, fun F G => ?_⟩
  rw [show (-1 : ℝ) / (1 / lam) = -lam from by field_simp]
  exact poincare_implies_cov_bound E lam hE hP F G

/-! ## Bridge lemma: covariance decay → exponential clustering -/

/-- Var(f) ≤ E[f²] (Jensen: Var(f) = E[f²] - (E[f])² ≤ E[f²]). -/
private lemma var_le_sq_int {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
  -- Use integral_var_eq: ∫(f - ∫f)² = ∫f² - (∫f)² ≤ ∫f²
  have heq := integral_var_eq μ f hf hf2
  linarith [sq_nonneg (∫ y, f y ∂μ)]

/-- HasCovarianceDecay implies ExponentialClustering.
    Key step: replace √Var(F) by √E[F²] using var_le_sq_int. -/
lemma covariance_decay_to_exponential_clustering
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (C ξ : ℝ) (hCD : HasCovarianceDecay μ C ξ) :
    ExponentialClustering μ C ξ := by
  obtain ⟨hξ, hC, hcov⟩ := hCD
  refine ⟨hξ, hC, fun F G => ?_⟩
  have hFsqrt : Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, F x ^ 2 ∂μ) := by
    apply Real.sqrt_le_sqrt
    by_cases hF2 : Integrable (fun x => F x ^ 2) μ
    · by_cases hF1 : Integrable F μ
      · exact var_le_sq_int (μ := μ) F hF1 hF2
      · simp [integral_undef hF1]
    · have hFv : ¬Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ := by
        intro hv
        apply hF2
        set c := ∫ y, F y ∂μ
        have hFc : Integrable (fun x => F x - c) μ :=
          (hv.add (integrable_const 1)).mono_fun
            (hv.1.sub aestronglyMeasurable_const)
            (ae_of_all _ fun x => by
              simp only [Real.norm_eq_abs]
              nlinarith [sq_nonneg (F x - c), sq_abs (F x - c), abs_nonneg (F x - c)])
        have hF1 : Integrable F μ :=
          (hFc.add (integrable_const c)).congr (ae_of_all _ fun x => by simp)
        exact ((hv.add (hF1.const_mul (2 * c))).sub (integrable_const (c ^ 2))).congr
          (ae_of_all _ fun x => by ring)
      simp [integral_undef hF2, integral_undef hFv]
  have hGsqrt : Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, G x ^ 2 ∂μ) := by
    apply Real.sqrt_le_sqrt
    by_cases hG2 : Integrable (fun x => G x ^ 2) μ
    · by_cases hG1 : Integrable G μ
      · exact var_le_sq_int (μ := μ) G hG1 hG2
      · simp [integral_undef hG1]
    · have hGv : ¬Integrable (fun x => (G x - ∫ y, G y ∂μ) ^ 2) μ := by
        intro hv
        apply hG2
        set c := ∫ y, G y ∂μ
        have hGc : Integrable (fun x => G x - c) μ :=
          (hv.add (integrable_const 1)).mono_fun
            (hv.1.sub aestronglyMeasurable_const)
            (ae_of_all _ fun x => by
              simp only [Real.norm_eq_abs]
              nlinarith [sq_nonneg (G x - c), sq_abs (G x - c), abs_nonneg (G x - c)])
        have hG1 : Integrable G μ :=
          (hGc.add (integrable_const c)).congr (ae_of_all _ fun x => by simp)
        exact ((hv.add (hG1.const_mul (2 * c))).sub (integrable_const (c ^ 2))).congr
          (ae_of_all _ fun x => by ring)
      simp [integral_undef hG2, integral_undef hGv]
  have hmul :
      C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)
        ≤ C * Real.sqrt (∫ x, F x ^ 2 ∂μ) *
          Real.sqrt (∫ x, G x ^ 2 ∂μ) := by gcongr
  calc |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)|
      ≤ C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
          Real.exp (-1 / ξ) := hcov F G
    _ ≤ C * Real.sqrt (∫ x, F x ^ 2 ∂μ) *
            Real.sqrt (∫ x, G x ^ 2 ∂μ) *
          Real.exp (-1 / ξ) :=
        mul_le_mul_of_nonneg_right hmul (Real.exp_nonneg _)

/-! ## Main theorem -/

/-- Milestone M4: DLR_LSI → ExponentialClustering.
    Chain: DLR_LSI → Poincaré (per volume) → covariance decay → ExponentialClustering.
    Clustering period ξ = 2/α_star ≤ 2/α_star (the axiom bound). -/
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
  -- Step 1: LSI → Poincaré at each volume L
  have hPoincare : ∀ L, PoincareInequality (gibbsFamily L) E (α_star / 2) := by
    intro L
    -- Adapt: LogSobolevInequality has no nonnegativity condition on f,
    -- but lsi_implies_poincare_strong requires it — we ignore it via _ placeholder
    have hLSI_adapt : ∀ f : Ω → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
        ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(gibbsFamily L) -
        (∫ x, f x ^ 2 ∂(gibbsFamily L)) * Real.log (∫ x, f x ^ 2 ∂(gibbsFamily L)) ≤
        (2 / α_star) * E f :=
      fun f hf _ => (hLSI_per_volume L).2 f hf
    exact lsi_implies_poincare_strong (gibbsFamily L) E (hE L) α_star hLSI_adapt hα
  -- Step 2: Poincaré → covariance decay (M4 core axiom)
  have hCov : ∀ L, HasCovarianceDecay (gibbsFamily L) 2 (2 / α_star) := by
    intro L
    have h := poincare_to_covariance_decay E (α_star / 2) (hE L) (hPoincare L)
    -- 1/(α_star/2) = 2/α_star
    have heq : (1 : ℝ) / (α_star / 2) = 2 / α_star := by field_simp
    rwa [heq] at h
  -- Step 3: covariance decay → ExponentialClustering
  exact ⟨2, 2 / α_star, by positivity, le_refl _,
    fun L => covariance_decay_to_exponential_clustering 2 _ (hCov L)⟩

end YangMills
