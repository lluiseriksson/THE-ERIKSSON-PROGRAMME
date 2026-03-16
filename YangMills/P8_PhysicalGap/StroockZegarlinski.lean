import Mathlib
import YangMills.P8_PhysicalGap.CovarianceLemmas
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.P8_PhysicalGap.PoincareCovarianceRoadmap
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

/-! ## Cauchy-Schwarz and covariance identity (Layer 3 of PoincareCovarianceRoadmap) -/

/-- (∫fg)² ≤ (∫f²)(∫g²) — squared Cauchy-Schwarz via quadratic polynomial argument.
    No measurability hypothesis: when ∫fg undefined (=0), bound holds trivially. -/
/-! ## Bridge axiom (M4 core) — decomposed -/
/-- Poincaré → covariance decay via MarkovSemigroup.
    Uses markov_to_covariance_decay (Layers 1+2+2b+3 of PoincareCovarianceRoadmap).
    Requires sg : MarkovSemigroup μ and integrability hypotheses on F, G, T₁G.
    The C=2 bound follows from C=1 by nlinarith. -/
theorem poincare_to_covariance_decay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hE : IsDirichletFormStrong E μ)
    (hP : PoincareInequality μ E lam)
    (hsg_F : ∀ F : Ω → ℝ,
      Integrable F μ →
      Integrable (fun x => F x ^ 2) μ →
      Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ →
      Integrable (fun x => sg.T 1 F x) μ ∧
      Integrable (fun x => (sg.T 1 F x - ∫ y, sg.T 1 F y ∂μ) ^ 2) μ)
    (hsg_FG : ∀ F G : Ω → ℝ,
      Integrable F μ → Integrable G μ →
      Integrable (fun x => F x ^ 2) μ →
      Integrable (fun x => G x ^ 2) μ →
      Integrable (fun x => F x * sg.T 1 G x) μ) :
    HasCovarianceDecay μ 2 (1 / lam) := by
  obtain ⟨hlam, _⟩ := hP
  refine ⟨by positivity, by norm_num, fun F G => ?_⟩
  rw [show (-1 : ℝ) / (1 / lam) = -lam from by field_simp]
  -- Get integrability hypotheses
  by_cases hF : Integrable F μ
  · by_cases hG : Integrable G μ
    · by_cases hF2 : Integrable (fun x => F x ^ 2) μ
      · by_cases hG2 : Integrable (fun x => G x ^ 2) μ
        · have hFv : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ := by
            have := sq_sub_int_implies_sq_int μ F hF.1 hF2
            simpa using this
          have hGv : Integrable (fun x => (G x - ∫ y, G y ∂μ) ^ 2) μ := by
            have := sq_sub_int_implies_sq_int μ G hG.1 hG2
            simpa using this
          obtain ⟨hT1G, hT1Gv⟩ := hsg_F G hG hG2 hGv
          have hFG := hsg_FG F G hF hG hF2 hG2
          have hbase := markov_to_covariance_decay sg E lam hE hP F G
            hF hG hFv hGv hFG hF2 hG2 hT1G hT1Gv
          nlinarith [Real.sqrt_nonneg (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ),
                     Real.sqrt_nonneg (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ),
                     Real.exp_nonneg (-lam), hbase,
                     mul_nonneg (mul_nonneg
                       (Real.sqrt_nonneg (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ))
                       (Real.sqrt_nonneg (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)))
                       (Real.exp_nonneg (-lam))]
        · simp [integral_undef hG2, Real.sqrt_zero, mul_zero]
      · simp [integral_undef hF2, Real.sqrt_zero, zero_mul]
    · simp [integral_undef hG, mul_zero]
  · simp [integral_undef hF, zero_mul]

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
    (sg : ∀ L, MarkovSemigroup (gibbsFamily L))
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
    have h := poincare_to_covariance_decay (sg L) E (α_star / 2) (hE L) (hPoincare L)
      (fun F hF hF2 hFv => ⟨(sg L).T_integrable 1 F hF,
        (sg L).T_sq_integrable 1 F hF2⟩)
      (fun F G hF hG hF2 hG2 => by exact (hF.mul ((sg L).T_integrable 1 G hG))
        |>.mono_fun ((hF.aestronglyMeasurable).mul
          ((sg L).T_integrable 1 G hG).aestronglyMeasurable)
          (ae_of_all _ fun x => by simp [Real.norm_eq_abs];
            nlinarith [sq_nonneg (F x), sq_nonneg ((sg L).T 1 G x)]))
    -- 1/(α_star/2) = 2/α_star
    have heq : (1 : ℝ) / (α_star / 2) = 2 / α_star := by field_simp
    rwa [heq] at h
  -- Step 3: covariance decay → ExponentialClustering
  exact ⟨2, 2 / α_star, by positivity, le_refl _,
    fun L => covariance_decay_to_exponential_clustering 2 _ (hCov L)⟩

end YangMills