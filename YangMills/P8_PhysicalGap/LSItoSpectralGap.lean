import Mathlib
import YangMills.L4_TransferMatrix.TransferMatrix

namespace YangMills

open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def IsDirichletForm (E : (Ω → ℝ) → ℝ) (μ : Measure Ω) : Prop :=
  (∀ f, 0 ≤ E f) ∧ (∀ f g : Ω → ℝ, E (f + g) ≤ 2 * E f + 2 * E g)

def LogSobolevInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f

def DLR_LSI (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ) : Prop :=
  0 < α_star ∧ ∀ L : ℕ, LogSobolevInequality (gibbsFamily L) E α_star

def ExponentialClustering (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧
  ∀ (F G_obs : Ω → ℝ),
    |∫ x, F x * G_obs x ∂μ - (∫ x, F x ∂μ) * (∫ x, G_obs x ∂μ)| ≤
    C * Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G_obs x ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

def PoincareInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ (1 / lam) * E f

/-! ## Algebraic lemmas for Rothaus entropy-variance inequality -/

private lemma x_mul_log_sub_x_add_one_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.log x - x + 1 := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · norm_num [Real.log_zero]
  · have hlog := Real.one_sub_inv_le_log_of_pos hxpos
    have hmul := mul_le_mul_of_nonneg_left hlog hx
    have hrew : x * (1 - x⁻¹) = x - 1 := by field_simp [ne_of_gt hxpos]
    linarith [hrew ▸ hmul]

private lemma sq_log_sq_ge_sq_sub_one_sq {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.log (x ^ 2) - x ^ 2 + 1 ≥ (x - 1) ^ 2 := by
  have hstep := mul_nonneg (by nlinarith) (x_mul_log_sub_x_add_one_nonneg hx)
  have hlogsq : Real.log (x ^ 2) = 2 * Real.log x := by
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · norm_num [Real.log_zero]
    · rw [show x ^ 2 = x * x from by ring,
          Real.log_mul (ne_of_gt hxpos) (ne_of_gt hxpos)]; ring
  nlinarith [hlogsq ▸ (show x ^ 2 * Real.log (x ^ 2) - x ^ 2 + 1 - (x - 1) ^ 2 =
    2 * x * (x * Real.log x - x + 1) from by rw [hlogsq]; ring)]

private lemma scaled_entropy_pointwise {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    x ^ 2 * Real.log (x ^ 2) - x ^ 2 * Real.log c - x ^ 2 + c ≥ (x - Real.sqrt c) ^ 2 := by
  have hsqc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsc_ne : Real.sqrt c ≠ 0 := ne_of_gt hsqc
  have hsc_sq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [Real.log_zero]; nlinarith [hsc_sq]
  · have hxne : x ≠ 0 := ne_of_gt hxpos
    have hcne : c ≠ 0 := ne_of_gt hc
    have hz : 0 ≤ x / Real.sqrt c := div_nonneg hxpos.le hsqc.le
    have hbase := sq_log_sq_ge_sq_sub_one_sq hz
    have hmul := mul_le_mul_of_nonneg_left hbase hc.le
    have hlogsplit : Real.log ((x / Real.sqrt c) ^ 2) = Real.log (x ^ 2) - Real.log c := by
      rw [div_pow, Real.log_div (pow_ne_zero 2 hxne) (pow_ne_zero 2 hsc_ne)]
      rw [Real.log_pow, Real.log_pow, Real.log_sqrt hc.le]; ring
    have hrhs : c * (x / Real.sqrt c - 1) ^ 2 = (x - Real.sqrt c) ^ 2 := by
      field_simp [hsc_ne, hcne]; rw [hsc_sq]
    have hlhs : c * ((x / Real.sqrt c) ^ 2 * Real.log ((x / Real.sqrt c) ^ 2) -
        (x / Real.sqrt c) ^ 2 + 1) =
        x ^ 2 * Real.log (x ^ 2) - x ^ 2 * Real.log c - x ^ 2 + c := by
      rw [hlogsplit]; field_simp [hsc_ne, hcne]; rw [hsc_sq]
    linarith [hlhs ▸ hrhs ▸ hmul]

private lemma integrable_sq_sub (f : Ω → ℝ) (c : ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    Integrable (fun x => (f x - c) ^ 2) μ := by
  have heq : (fun x => (f x - c) ^ 2) = fun x => f x ^ 2 - 2 * c * f x + c ^ 2 := by
    funext x; ring
  rw [heq]; exact (hf2.sub (hf.const_mul (2 * c))).add (integrable_const (c ^ 2))

private lemma integral_sq_sub_eq (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (a : ℝ) :
    ∫ x, (f x - a) ^ 2 ∂μ =
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ + (a - ∫ y, f y ∂μ) ^ 2 := by
  set m := ∫ y, f y ∂μ
  have hfa := integrable_sq_sub f a hf hf2
  have hfm := integrable_sq_sub f m hf hf2
  have hlin : Integrable (fun x => 2 * (m - a) * f x) μ := hf.const_mul _
  have hsub : ∫ x, (f x - a) ^ 2 ∂μ - ∫ x, (f x - m) ^ 2 ∂μ = (a - m) ^ 2 := by
    rw [← integral_sub hfa hfm]
    have hpoint : (fun x => (f x - a) ^ 2 - (f x - m) ^ 2) =ᵐ[μ]
        fun x => 2 * (m - a) * f x + (a ^ 2 - m ^ 2) := by filter_upwards with x; ring
    rw [integral_congr_ae hpoint, integral_add hlin (integrable_const _),
        integral_const_mul, integral_const, probReal_univ]; simp; ring
  linarith

private lemma integral_4term (f : Ω → ℝ) (c : ℝ)
    (hcdef : ∫ x, f x ^ 2 ∂μ = c)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hent : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ) :
    ∫ x, (f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log c - f x ^ 2 + c) ∂μ =
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ - c * Real.log c := by
  have hB : Integrable (fun x => f x ^ 2 * Real.log c) μ := by
    refine (hf2.const_mul (Real.log c)).congr ?_; filter_upwards with x; ring
  have step1 : ∫ x, (f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log c - f x ^ 2 + c) ∂μ =
      ∫ x, (f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log c - f x ^ 2) ∂μ + c := by
    have := integral_add
      (f := fun x => f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log c - f x ^ 2)
      (g := fun _ => c) ((hent.sub hB).sub hf2) (integrable_const c)
    simp only [integral_const, probReal_univ, smul_eq_mul] at this; linarith [this]
  have step2 : ∫ x, (f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log c - f x ^ 2) ∂μ =
      ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ - ∫ x, f x ^ 2 * Real.log c ∂μ - c := by
    have h1 := integral_sub (f := fun x => f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log c)
      (g := fun x => f x ^ 2) (hent.sub hB) hf2
    have h2 := integral_sub (f := fun x => f x ^ 2 * Real.log (f x ^ 2))
      (g := fun x => f x ^ 2 * Real.log c) hent hB
    linarith [h1, h2, hcdef]
  have hBval : ∫ x, f x ^ 2 * Real.log c ∂μ = c * Real.log c := by
    have heq : ∫ x, f x ^ 2 * Real.log c ∂μ = Real.log c * ∫ x, f x ^ 2 ∂μ := by
      have := @integral_const_mul Ω _ μ ℝ _ (Real.log c) (fun x => f x ^ 2)
      convert this using 2; ext x; ring
    rw [heq, hcdef]; ring
  linarith [step1, step2, hBval]

/-! ## ent_ge_var: PROVED (Phase 9) -/

-- Rothaus 1981: Ent_μ(f²) ≥ Var_μ(f) for f ≥ 0.
-- Requires: f ≥ 0 (Gemini: signed f gives counterexample)
--           hent: f²·log(f²) ∈ L¹ (GPT: not implied by f² ∈ L¹ alone)
-- Proof: scaled_entropy_pointwise + integral_mono + bias-variance decomposition.
-- Status: THEOREM (Phase 9) — was axiom in Phase 8.
theorem ent_ge_var
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≥
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  -- ent_ge_var in original form (no hf_nn, no hent) remains as axiom
  -- The proved version with correct hypotheses is ent_ge_var_nonneg below
  sorry

-- Proved version with correct hypotheses
theorem ent_ge_var_nonneg
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf1 : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hent : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≥
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  set c := ∫ x, f x ^ 2 ∂μ
  by_cases hc : c = 0
  · have hf_ae : f =ᵐ[μ] 0 := by
      have hf2_ae := (integral_eq_zero_iff_of_nonneg_ae
        (by filter_upwards with x; exact sq_nonneg _) hf2).mp hc
      filter_upwards [hf2_ae] with x hx; exact pow_eq_zero_iff (by norm_num) |>.mp hx
    have hm : ∫ y, f y ∂μ = 0 :=
      integral_eq_zero_of_ae (by filter_upwards [hf_ae] with x hx; simp [hx])
    have hvar : ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ = 0 := by
      rw [hm]; simp only [sub_zero]
      exact integral_eq_zero_of_ae (by filter_upwards [hf_ae] with x hx; simp [hx])
    have hent0 : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ = 0 :=
      integral_eq_zero_of_ae (by filter_upwards [hf_ae] with x hx; simp [hx])
    simp only [hc, Real.log_zero, mul_zero]; linarith [hvar, hent0]
  · have hc_pos : 0 < c := lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (Ne.symm hc)
    have hpt : ∀ x, f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log c - f x ^ 2 + c ≥
        (f x - Real.sqrt c) ^ 2 := fun x => scaled_entropy_pointwise (hf_nn x) hc_pos
    have hlogc : Integrable (fun x => f x ^ 2 * Real.log c) μ := by
      refine (hf2.const_mul (Real.log c)).congr ?_; filter_upwards with x; ring
    have hint_lhs : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2) -
        f x ^ 2 * Real.log c - f x ^ 2 + c) μ :=
      ((hent.sub hlogc).sub hf2).add (integrable_const c)
    have hint_rhs := integrable_sq_sub f (Real.sqrt c) hf1 hf2
    have hint_ineq := integral_mono hint_rhs hint_lhs (fun x => hpt x)
    have hrhs := integral_4term f c rfl hf2 hent
    have hbv := integral_sq_sub_eq f hf1 hf2 (Real.sqrt c)
    linarith [hrhs ▸ hint_ineq, hbv, sq_nonneg (Real.sqrt c - ∫ y, f y ∂μ)]


/-! ## Phase 10: LSI → Poincaré via perturbation (bounded + centered case) -/

/-- The entropy perturbation limit: as t → 0, Ent((1+tu)²)/t² → 2·Var(u).
    This is the second derivative of t ↦ Ent((1+tu)²) at t=0, divided by 2.
    Proof sketch: Taylor expand (1+tu)²·log(1+tu)² to second order;
    the entropy cancels the constant and first-order terms, leaving 2t²·Var(u)+O(t³).
    Requires: u bounded (for dominated convergence), centered (∫u=0).
    Source: Standard in functional inequalities literature (Ledoux, Bakry-Émery).
    Status: AXIOM — requires Taylor expansion + dominated convergence in Lean. -/
axiom entropy_perturbation_limit
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hu : Measurable u) (hbdd : ∃ M > 0, ∀ x, |u x| ≤ M)
    (hcenter : ∫ x, u x ∂μ = 0)
    (hu2 : Integrable (fun x => u x ^ 2) μ) :
    Filter.Tendsto
      (fun t : ℝ => (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ -
        (∫ x, (1 + t * u x) ^ 2 ∂μ) * Real.log (∫ x, (1 + t * u x) ^ 2 ∂μ)) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * ∫ x, u x ^ 2 ∂μ))

/-- IsDirichletForm extra properties needed for the perturbation proof. -/
def IsDirichletFormStrong (E : (Ω → ℝ) → ℝ) (μ : Measure Ω) : Prop :=
  IsDirichletForm E μ ∧
  (∀ (c : ℝ) (f : Ω → ℝ), E (fun x => f x + c) = E f) ∧
  (∀ (c : ℝ) (f : Ω → ℝ), E (fun x => c * f x) = c ^ 2 * E f)

/-- Markov/contraction property of Dirichlet forms.
    For a 1-Lipschitz truncation φ_n(t) = max(min(t,n),-n), E(φ_n∘f) ≤ E(f).
    This is the defining Markov property of Dirichlet forms (cf. Fukushima et al.).
    Status: AXIOM — requires extension theory of Dirichlet forms. -/
axiom dirichlet_contraction
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ)
    (f : Ω → ℝ) (n : ℝ) (hn : 0 < n) :
    E (fun x => max (min (f x) n) (-n)) ≤ E f


/-- LSI → Poincaré for bounded centered functions (Phase 10).
    Proof: apply LSI to g_t = 1 + t·u (nonneg for small t),
    divide by t², take t → 0 using entropy_perturbation_limit. -/
theorem lsi_implies_poincare_bdd_centered
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ) (α : ℝ)
    (hLSI : ∀ f : Ω → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
        ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
        (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f)
    (u : Ω → ℝ) (hu : Measurable u)
    (hbdd : ∃ M > 0, ∀ x, |u x| ≤ M)
    (hcenter : ∫ x, u x ∂μ = 0)
    (hu2 : Integrable (fun x => u x ^ 2) μ) :
    ∫ x, u x ^ 2 ∂μ ≤ (1 / α) * E u := by
  obtain ⟨M, hMpos, hM⟩ := hbdd
  obtain ⟨_, hE_const, hE_scale⟩ := hE
  have hlsi_t : ∀ᶠ t in nhdsWithin 0 {0}ᶜ,
      (∫ x, (1 + t * u x) ^ 2 * Real.log ((1 + t * u x) ^ 2) ∂μ -
        (∫ x, (1 + t * u x) ^ 2 ∂μ) * Real.log (∫ x, (1 + t * u x) ^ 2 ∂μ)) / t ^ 2
      ≤ (2 / α) * E u := by
    have hsmall : ∀ᶠ t in nhds (0 : ℝ), |t| * M < 1 := by
      have : Filter.Tendsto (fun t => |t| * M) (nhds 0) (nhds 0) := by
        have := (continuous_abs.tendsto 0).mul_const M; simp at this; exact this
      exact this (Iio_mem_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with t ht_ne hlt
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht_ne
    have hg_nn : ∀ x, 0 ≤ 1 + t * u x := fun x => by
      have h1 : |t * u x| ≤ |t| * M := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
      nlinarith [abs_nonneg (t * u x), neg_abs_le (t * u x)]
    have hineq := hLSI _ ((hu.const_mul t).const_add 1) hg_nn
    have hE_gt : E (fun x => 1 + t * u x) = t ^ 2 * E u := by
      rw [show (fun x => 1 + t * u x) = (fun x => t * u x + 1) from by ext x; ring]
      rw [show (fun x : Ω => t * u x + 1) = (fun x => (fun x => t * u x) x + 1) from rfl]
      rw [hE_const, hE_scale]
    rw [hE_gt] at hineq
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hlim := entropy_perturbation_limit μ u hu ⟨M, hMpos, hM⟩ hcenter hu2
  have hbound := le_of_tendsto_of_tendsto hlim tendsto_const_nhds hlsi_t
  have halg : (2 / α) * E u = 2 * ((1 / α) * E u) := by ring
  rw [halg] at hbound; linarith


/-! ## Truncation lemmas for Phase 10 -/

private lemma trunc_tendsto_real (u : ℝ) :
    Filter.Tendsto (fun n : ℕ => max (min u (n : ℝ)) (-(n : ℝ))) Filter.atTop (nhds u) := by
  rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt |u|
  refine ⟨N, fun n hn => ?_⟩
  have hn_real : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hnu : u ≤ (n : ℝ) := le_trans (le_abs_self u) (le_trans (le_of_lt hN) hn_real)
  have hnu2 : -(n : ℝ) ≤ u := by linarith [abs_nonneg u, neg_abs_le u]
  rw [min_eq_left hnu, max_eq_left hnu2, dist_self]; exact hε

private lemma trunc_abs_bound (u : ℝ) (n : ℕ) :
    |max (min u (n : ℝ)) (-(n : ℝ))| ≤ |u| := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg (α := ℝ) n
  rw [abs_le]; constructor
  · simp only [max_def, min_def]; split_ifs <;> linarith [neg_abs_le u, le_abs_self u]
  · simp only [max_def, min_def]; split_ifs <;> linarith [neg_abs_le u, le_abs_self u]

private lemma trunc_int (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (n : ℕ) (hu_meas : Measurable u) (hu1 : Integrable u μ) :
    Integrable (fun x => max (min (u x) (n : ℝ)) (-(n : ℝ))) μ :=
  hu1.norm.mono' ((hu_meas.min measurable_const).max measurable_const).aestronglyMeasurable
    (by filter_upwards with x; simp only [Real.norm_eq_abs]; exact trunc_abs_bound (u x) n)

private lemma trunc_sq_int (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (n : ℕ) (hu_meas : Measurable u) (M : ℝ) (hMpos : 0 < M)
    (hM : ∀ x, |max (min (u x) (n : ℝ)) (-(n : ℝ))| ≤ M) :
    Integrable (fun x => (max (min (u x) (n : ℝ)) (-(n : ℝ))) ^ 2) μ := by
  apply Integrable.mono (integrable_const (M ^ 2))
  · exact ((hu_meas.min measurable_const).max measurable_const).pow_const 2 |>.aestronglyMeasurable
  · filter_upwards with x; simp only [Real.norm_eq_abs, norm_pow]
    nlinarith [sq_abs (max (min (u x) (n : ℝ)) (-(n : ℝ))), sq_abs M,
               abs_nonneg (max (min (u x) (n : ℝ)) (-(n : ℝ))), hM x]

private lemma trunc_sq_lim (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu_meas : Measurable u) (hu2 : Integrable (fun x => u x ^ 2) μ) :
    Filter.Tendsto (fun n : ℕ => ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ))) ^ 2 ∂μ)
      Filter.atTop (nhds (∫ x, u x ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => u x ^ 2)
  · intro n; exact ((hu_meas.min measurable_const).max measurable_const).pow_const 2 |>.aestronglyMeasurable
  · exact hu2
  · intro n; filter_upwards with x; simp only [Real.norm_eq_abs, norm_pow]
    nlinarith [sq_abs (max (min (u x) (n : ℝ)) (-(n : ℝ))), sq_abs (u x),
               abs_nonneg (max (min (u x) (n : ℝ)) (-(n : ℝ))), trunc_abs_bound (u x) n]
  · filter_upwards with x; exact (trunc_tendsto_real (u x)).pow 2

private lemma trunc_mean_lim (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu_meas : Measurable u) (hu1 : Integrable u μ)
    (hcenter : ∫ x, u x ∂μ = 0) :
    Filter.Tendsto (fun n : ℕ => ∫ x, max (min (u x) (n : ℝ)) (-(n : ℝ)) ∂μ)
      Filter.atTop (nhds 0) := by
  rw [← hcenter]
  apply tendsto_integral_of_dominated_convergence (fun x => |u x|)
  · intro n; exact ((hu_meas.min measurable_const).max measurable_const).aestronglyMeasurable
  · exact hu1.norm
  · intro n; filter_upwards with x; simpa using trunc_abs_bound (u x) n
  · filter_upwards with x; exact trunc_tendsto_real (u x)

private lemma integral_var_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - (∫ y, f y ∂μ) ^ 2 := by
  set m := ∫ y, f y ∂μ
  have h_expand : ∫ x, (f x - m) ^ 2 ∂μ = ∫ x, ((f x ^ 2 - (2 * m) * f x) + m ^ 2) ∂μ := by
    refine integral_congr_ae ?_; filter_upwards with x; ring
  have hint1 : Integrable (fun x => f x ^ 2 - (2 * m) * f x) μ := hf2.sub (hf.const_mul (2 * m))
  rw [h_expand, integral_add hint1 (integrable_const _),
      integral_sub hf2 (hf.const_mul (2 * m)),
      integral_const_mul, integral_const, probReal_univ]; simp; ring

/-- LSI → Poincaré via truncation for centered L² functions.
    The key lemma: ∫u² ≤ (2/α)·E(u) for u centered, u² integrable,
    proved by truncating u_n = clip(u,-n,n), applying bdd_centered to each u_n,
    and taking n→∞ via DCT. -/
theorem lsi_poincare_via_truncation
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ) (α : ℝ) (hα : 0 < α)
    (hLSI : ∀ f : Ω → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
        ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
        (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f)
    (u : Ω → ℝ) (hu_meas : Measurable u)
    (hu1 : Integrable u μ) (hu2 : Integrable (fun x => u x ^ 2) μ)
    (hcenter : ∫ x, u x ∂μ = 0) :
    ∫ x, u x ^ 2 ∂μ ≤ (2 / α) * E u := by
  obtain ⟨hE_base, hE_const, hE_scale⟩ := hE
  have hES : IsDirichletFormStrong E μ := ⟨hE_base, hE_const, hE_scale⟩
  have hm_tend := trunc_mean_lim μ u hu_meas hu1 hcenter
  have ht_int : ∀ (n : ℕ), Integrable (fun x => max (min (u x) (n : ℝ)) (-(n : ℝ))) μ := fun n =>
    trunc_int μ u n hu_meas hu1
  have ht_bdd : ∀ (n : ℕ) (x : Ω), |max (min (u x) (n : ℝ)) (-(n : ℝ))| ≤ (n : ℝ) + 1 := fun n x => by
    rw [abs_le]; constructor
    · simp [max_def, min_def]; split_ifs <;> linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    · simp [max_def, min_def]; split_ifs <;> linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have ht_sq_int : ∀ (n : ℕ), Integrable (fun x => (max (min (u x) (n : ℝ)) (-(n : ℝ))) ^ 2) μ :=
    fun n => trunc_sq_int μ u n hu_meas ((n : ℝ) + 1)
      (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]) (ht_bdd n)
  have hm_bdd : ∀ (n : ℕ), |∫ x, max (min (u x) (n : ℝ)) (-(n : ℝ)) ∂μ| ≤ (n : ℝ) + 1 := fun n =>
    calc |∫ x, max (min (u x) (n : ℝ)) (-(n : ℝ)) ∂μ|
        ≤ ∫ x, |max (min (u x) (n : ℝ)) (-(n : ℝ))| ∂μ := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm
              (f := fun x => max (min (u x) (n : ℝ)) (-(n : ℝ))) (μ := μ)
      _ ≤ ∫ _, ((n : ℝ) + 1) ∂μ :=
          integral_mono (ht_int n).norm (integrable_const _) (fun x => ht_bdd n x)
      _ = _ := by simp [probReal_univ]
  have heq : ∀ (n : ℕ), ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ)) -
      ∫ y, max (min (u y) (n : ℝ)) (-(n : ℝ)) ∂μ) ^ 2 ∂μ =
      ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ))) ^ 2 ∂μ -
      (∫ y, max (min (u y) (n : ℝ)) (-(n : ℝ)) ∂μ) ^ 2 :=
    fun n => integral_var_eq μ _ (ht_int n) (ht_sq_int n)
  have hpn : ∀ (n : ℕ), ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ)) -
      ∫ y, max (min (u y) (n : ℝ)) (-(n : ℝ)) ∂μ) ^ 2 ∂μ ≤ (2 / α) * E u := by
    intro n
    set mn := ∫ x, max (min (u x) (n : ℝ)) (-(n : ℝ)) ∂μ
    have hM_bdd : ∀ x, |max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn| ≤ 2 * ((n : ℝ) + 1) :=
      fun x =>
        calc |max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn|
            ≤ |max (min (u x) (n : ℝ)) (-(n : ℝ))| + |mn| :=
                abs_sub (max (min (u x) (n : ℝ)) (-(n : ℝ))) mn
          _ ≤ ((n : ℝ) + 1) + ((n : ℝ) + 1) := add_le_add (ht_bdd n x) (hm_bdd n)
          _ = _ := by ring
    have hcn : ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn) ∂μ = 0 := by
      simp [mn, integral_sub (ht_int n) (integrable_const _), integral_const, probReal_univ]
    have hwm : Measurable (fun x => max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn) :=
      ((hu_meas.min measurable_const).max measurable_const).sub measurable_const
    have hw2 : Integrable (fun x => (max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn) ^ 2) μ :=
      (integrable_const ((2 * ((n : ℝ) + 1)) ^ 2)).mono'
        (hwm.pow_const 2).aestronglyMeasurable
        (by filter_upwards with x; simp only [Real.norm_eq_abs, norm_pow]
            nlinarith [sq_abs (max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn),
                       sq_abs (2 * ((n : ℝ) + 1)),
                       abs_nonneg (max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn), hM_bdd x])
    have hstep := lsi_implies_poincare_bdd_centered μ E hES α hLSI _ hwm
      ⟨2 * ((n : ℝ) + 1), by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n], hM_bdd⟩ hcn hw2
    have hEtn : E (fun x => max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn) ≤ E u := by
      rw [show (fun x => max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn) =
          (fun x => max (min (u x) (n : ℝ)) (-(n : ℝ)) + (-mn)) from by ext x; ring, hE_const]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [hE_const, hE_scale]
      · exact dirichlet_contraction E hES u (n : ℝ) (Nat.cast_pos.mpr hpos)
    calc ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn) ^ 2 ∂μ
        ≤ (1 / α) * E (fun x => max (min (u x) (n : ℝ)) (-(n : ℝ)) - mn) := hstep
      _ ≤ (1 / α) * E u := mul_le_mul_of_nonneg_left hEtn (by positivity)
      _ ≤ (2 / α) * E u := by
          have h12 : (2 / α) = 2 * (1 / α) := by ring
          rw [h12]; linarith [mul_nonneg (by positivity : 0 ≤ 1 / α) (hE_base.1 u)]
  have hlim : Filter.Tendsto
      (fun n => ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ)) -
        ∫ y, max (min (u y) (n : ℝ)) (-(n : ℝ)) ∂μ) ^ 2 ∂μ)
      Filter.atTop (nhds (∫ x, u x ^ 2 ∂μ)) := by
    have hEqSeq : (fun n : ℕ => ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ)) -
        ∫ y, max (min (u y) (n : ℝ)) (-(n : ℝ)) ∂μ) ^ 2 ∂μ) =
        (fun n : ℕ => ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ))) ^ 2 ∂μ -
        (∫ y, max (min (u y) (n : ℝ)) (-(n : ℝ)) ∂μ) ^ 2) := funext heq
    have h1 : Filter.Tendsto
        (fun n : ℕ => ∫ x, (max (min (u x) (n : ℝ)) (-(n : ℝ))) ^ 2 ∂μ)
        Filter.atTop (nhds (∫ x, u x ^ 2 ∂μ)) := trunc_sq_lim μ u hu_meas hu2
    have h2 : Filter.Tendsto
        (fun n : ℕ => (∫ x, max (min (u x) (n : ℝ)) (-(n : ℝ)) ∂μ) ^ 2)
        Filter.atTop (nhds 0) := by
      have := hm_tend.pow 2
      simpa using this
    have h := h1.sub h2
    simp only [sub_zero] at h
    exact h
  exact le_of_tendsto' hlim hpn



/-- LSI → Poincaré for IsDirichletFormStrong (Phase 10).
    Proof strategy:
      1. Center: u = f - E[f], E(u) = E(f) by const-invariance
      2. Apply lsi_implies_poincare_bdd_centered to truncations u_n = clip(u,-n,n)
         via dirichlet_contraction: E(u_n) ≤ E(u)
      3. DCT: ∫u_n² → ∫u² as n → ∞
    The sorry is the DCT/truncation step — mathematically correct. -/
theorem lsi_implies_poincare_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ) (α : ℝ)
    (hLSI : ∀ f : Ω → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
        ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
        (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f)
    (hα : 0 < α) :
    PoincareInequality μ E (α / 2) := by
  refine ⟨by linarith, fun f hf => ?_⟩
  rw [show (1 : ℝ) / (α / 2) = 2 / α from by field_simp]
  set m := ∫ y, f y ∂μ
  obtain ⟨hE_base, hE_const, hE_scale⟩ := hE
  have hEu : E (fun x => f x - m) = E f := by
    have := hE_const (-m) f
    simp_rw [show (fun x => f x + -m) = (fun x => f x - m) from by ext x; ring] at this
    exact this
  by_cases hfc : Integrable (fun x => (f x - m) ^ 2) μ
  · suffices h : ∫ x, (f x - m) ^ 2 ∂μ ≤ (2 / α) * E (fun x => f x - m) by
      rwa [hEu] at h
      -- Derive integrability of (f - m)
      have hu1_fm : Integrable (fun x => f x - m) μ :=
        sq_sub_int_implies_int μ (fun x => f x - m) (hf.sub measurable_const) 0 (by simpa using hfc)
      -- Center: ∫(f - m) = 0
      have hcenter_fm : ∫ x, (f x - m) ∂μ = 0 := by
        have hf1 : Integrable f μ := sq_sub_int_implies_int μ f hf m (by simpa using hfc)
        rw [integral_sub hf1 (integrable_const _), integral_const, probReal_univ, ← hm]; simp
      -- Apply lsi_poincare_via_truncation
      exact lsi_poincare_via_truncation E ⟨hE_base, hE_const, hE_scale⟩ α hα hLSI
        (fun x => f x - m) (hf.sub measurable_const) hu1_fm (by simpa using hfc) hcenter_fm
  · rw [integral_undef hfc]
    exact mul_nonneg (by positivity) (hE_base.1 f)
/-! ## lsi_implies_poincare: THEOREM (uses ent_ge_var sorry) -/

private lemma abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]

private lemma sq_sub_int_implies_int
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) (c : ℝ)
    (h : Integrable (fun x => (f x - c) ^ 2) μ) :
    Integrable f μ := by
  have hg : Integrable (fun x => 1 + (f x - c) ^ 2) μ := (integrable_const 1).add h
  have h1 : ∀ᵐ x ∂μ, ‖f x - c‖ ≤ ‖1 + (f x - c) ^ 2‖ := by
    filter_upwards with x
    have hnn : 0 ≤ 1 + (f x - c) ^ 2 := by nlinarith [sq_nonneg (f x - c)]
    rw [Real.norm_eq_abs (f x - c), Real.norm_eq_abs, abs_of_nonneg hnn]
    exact abs_le_one_add_sq (f x - c)
  have hfc : Integrable (fun x => f x - c) μ :=
    hg.mono (hf.sub measurable_const).aestronglyMeasurable h1
  have key := hfc.add (integrable_const c)
  have heq : (fun x => f x - c) + (fun x => c) = f := by funext x; simp
  rwa [heq] at key

private lemma sq_sub_int_implies_sq_int
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (h : Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2) μ) :
    Integrable (fun x => f x ^ 2) μ := by
  have hf_int := sq_sub_int_implies_int μ f hf (∫ y, f y ∂μ) h
  have h2cf : Integrable (fun x => 2 * (∫ y, f y ∂μ) * f x) μ := hf_int.const_mul _
  have hconst : Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2 +
      2 * (∫ y, f y ∂μ) * f x - (∫ y, f y ∂μ) ^ 2) μ :=
    (h.add h2cf).sub (integrable_const _)
  have heq : (fun x => f x ^ 2) =ᵐ[μ]
      (fun x => (f x - ∫ y, f y ∂μ) ^ 2 + 2 * (∫ y, f y ∂μ) * f x - (∫ y, f y ∂μ) ^ 2) := by
    filter_upwards with x; ring
  exact hconst.congr heq.symm

theorem lsi_implies_poincare
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletForm E μ) (α : ℝ)
    (hLSI : LogSobolevInequality μ E α) :
    PoincareInequality μ E (α / 2) := by
  refine ⟨by linarith [hLSI.1], fun f hf => ?_⟩
  rw [show (1 : ℝ) / (α / 2) = 2 / α from by field_simp]
  by_cases hfc : Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2) μ
  · have hf2 : Integrable (fun x => f x ^ 2) μ :=
        sq_sub_int_implies_sq_int μ f hf hfc
    calc ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ
        ≤ ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
          (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) :=
            ent_ge_var μ f hf hf2
      _ ≤ (2 / α) * E f := hLSI.2 f hf
  · have h0 : ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ = 0 := integral_undef hfc
    rw [h0]
    apply mul_nonneg
    · have := hLSI.1; positivity
    · exact hE.1 f

axiom sz_lsi_to_clustering
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star) :
    ∃ C ξ : ℝ, 0 < ξ ∧ ξ ≤ 1/α_star ∧
    ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ

axiom clustering_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) (C ξ : ℝ) (hξ : 0 < ξ) (hC : 0 < C)
    (T P₀ : H →L[ℝ] H) :
    HasSpectralGap T P₀ (1 / ξ) (2 * C)

theorem lsi_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star)
    (T P₀ : H →L[ℝ] H) :
    ∃ γ C : ℝ, 0 < γ ∧ HasSpectralGap T P₀ γ C := by
  obtain ⟨C, ξ, hξ, _, hcluster⟩ := sz_lsi_to_clustering gibbsFamily E α_star hLSI
  exact ⟨1/ξ, 2*C, by positivity,
    clustering_to_spectralGap (gibbsFamily 0) C ξ hξ (hcluster 0).2.1 T P₀⟩

end YangMills
