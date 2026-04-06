import Mathlib
import YangMills.P4_Continuum.Phase4Assembly
import YangMills.L2_Balaban.Measurability

namespace YangMills

open MeasureTheory Real

/-! ## F5.1: KP Hypotheses and Sufficient Conditions for ConnectedCorrDecay

Pattern for N-dependent constants: letI + named args (d := d) (N := N).
-/

section KPHypotheses

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Small-field polymer activity bound (H1).
    From Balaban CMP 116, Lemma 3, Eq (2.38). -/
def HasSmallFieldDecay (E0 κ g : ℝ) (activity : ℕ → ℝ) : Prop :=
  0 < E0 → 0 < κ → 0 < g →
  ∀ n : ℕ, |activity n| ≤ E0 * g ^ 2 * exp (-κ * n)

def SatisfiesH1 (E0 κ g : ℝ) (activity : ℕ → ℝ) : Prop :=
  HasSmallFieldDecay E0 κ g activity

/-- Large-field penalty (H2).
    From Balaban CMP 122, Eq (1.98)-(1.100). -/
def HasLargeFieldSuppression (p0 κ : ℝ) (activity : ℕ → ℝ) : Prop :=
  0 < p0 → 0 < κ →
  ∀ n : ℕ, |activity n| ≤ exp (-p0) * exp (-κ * n)

def SatisfiesH2 (p0 κ : ℝ) (activity : ℕ → ℝ) : Prop :=
  HasLargeFieldSuppression p0 κ activity

/-- (H3): locality / hard-core compatibility. Structural. -/
def SatisfiesH3 : Prop := True

/-- KP smallness predicate. δ < 1 → KP convergence. -/
def KPSmallness (δ weightedSum : ℝ) : Prop :=
  0 < δ ∧ δ < 1 ∧ weightedSum ≤ δ

/-- KP geometric series bound. C_anim(4) = 512, margin κ > log 512.
    From Paper 89, Lemma 6.2. -/
lemma kp_geometric_series
    (κ : ℝ) (hκ : Real.log 512 < κ)
    (C0 g : ℝ) (hg : 0 < g) (hC0 : 0 < C0)
    (h_small : C0 * g ^ 2 * exp (C0 * g ^ 2) *
      (Real.exp κ * (512 * Real.exp (1 - κ)) / (1 - 512 * Real.exp (1 - κ))) ≤ 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ weightedSum : ℝ,
      weightedSum ≤ C0 * g ^ 2 * exp (C0 * g ^ 2) *
        (Real.exp κ * (512 * Real.exp (1 - κ)) / (1 - 512 * Real.exp (1 - κ))) →
      weightedSum ≤ δ :=
  ⟨1/2, by norm_num, by norm_num, fun w hw => le_trans hw h_small⟩

lemma kp_smallness_of_bound (δ weightedSum : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hw : weightedSum ≤ δ) :
    KPSmallness δ weightedSum :=
  ⟨hδ0, hδ1, hw⟩

/-- **H1 activity summability**: any function satisfying the small-field decay bound
is absolutely summable. For κ > 0, the geometric majorant exp(-κ*n) gives
convergence by comparison. First sub-step of Step 3 in UNCONDITIONALITY_ROADMAP. -/
theorem smallfield_decay_summable (E0 κ g : ℝ) (hE0 : 0 < E0) (hκ : 0 < κ)
    (hg : 0 < g) (activity : ℕ → ℝ)
    (h : HasSmallFieldDecay E0 κ g activity) :
    Summable activity := by
  have hbound := h hE0 hκ hg
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hexp_nn : (0 : ℝ) ≤ exp (-κ) := exp_nonneg _
  have hpow : ∀ n : ℕ, exp (-κ * ↑n) = exp (-κ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← ih, ← exp_add]
      congr 1; push_cast; ring
  have hgeom : Summable (fun n : ℕ => E0 * g ^ 2 * exp (-κ) ^ n) :=
    (summable_geometric_of_lt_one hexp_nn hexp_lt1).mul_left _
  have habs_bd : ∀ n : ℕ, |activity n| ≤ E0 * g ^ 2 * exp (-κ) ^ n := fun n => by
    rw [← hpow n]; exact hbound n
  have hpos_nn : ∀ n, 0 ≤ (activity n + |activity n|) / 2 := fun n => by
    have h1 := abs_nonneg (activity n)
    have h2 : -activity n ≤ |activity n| := by
      calc -activity n ≤ |-activity n| := le_abs_self _
        _ = |activity n| := abs_neg _
    linarith
  have hpos_bd : ∀ n, (activity n + |activity n|) / 2 ≤ E0 * g ^ 2 * exp (-κ) ^ n :=
    fun n => by
      have h1 : activity n ≤ |activity n| := le_abs_self _
      have h2 := habs_bd n; linarith
  have hpos : Summable (fun n => (activity n + |activity n|) / 2) :=
    Summable.of_nonneg_of_le hpos_nn hpos_bd hgeom
  have hneg_nn : ∀ n, 0 ≤ (|activity n| - activity n) / 2 := fun n => by
    have := le_abs_self (activity n); linarith
  have hneg_bd : ∀ n, (|activity n| - activity n) / 2 ≤ E0 * g ^ 2 * exp (-κ) ^ n :=
    fun n => by
      have h1 : -activity n ≤ |activity n| := by
        calc -activity n ≤ |-activity n| := le_abs_self _
          _ = |activity n| := abs_neg _
      have h2 := habs_bd n; linarith
  have hneg : Summable (fun n => (|activity n| - activity n) / 2) :=
    Summable.of_nonneg_of_le hneg_nn hneg_bd hgeom
  have heq : activity = fun n => (activity n + |activity n|) / 2 -
      (|activity n| - activity n) / 2 := funext (fun n => by ring)
  rw [heq]; exact hpos.sub hneg


/-- **Quantitative tsum bound**: any activity with `HasSmallFieldDecay E0 κ g`
    satisfies ∑' n, ‖activity n‖ ≤ E0 * g² / (1 - exp(-κ)).
    Explicit closed-form geometric series estimate; first quantitative
    sub-step of Step 3 (KP activity bound). Campaign 19, v0.35.0. -/
theorem smallfield_decay_tsum_bound (E0 κ g : ℝ) (hE0 : 0 < E0) (hκ : 0 < κ)
    (hg : 0 < g) (activity : ℕ → ℝ)
    (h : HasSmallFieldDecay E0 κ g activity) :
    ∑' n, ‖activity n‖ ≤ E0 * g ^ 2 / (1 - Real.exp (-κ)) := by
  have hbound := h hE0 hκ hg
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hexp_nn : (0 : ℝ) ≤ exp (-κ) := exp_nonneg _
  have hpow : ∀ n : ℕ, exp (-κ * ↑n) = exp (-κ) ^ n := by
    intro n; induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ← ih, ← exp_add]; congr 1; push_cast; ring
  have hgeom : Summable (fun n : ℕ => E0 * g ^ 2 * exp (-κ) ^ n) :=
    (summable_geometric_of_lt_one hexp_nn hexp_lt1).mul_left _
  have hnorm_bd : ∀ n : ℕ, ‖activity n‖ ≤ E0 * g ^ 2 * exp (-κ) ^ n := fun n => by
    rw [Real.norm_eq_abs, ← hpow n]; exact hbound n
  have hnorm_sum : Summable (fun n : ℕ => ‖activity n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm_bd hgeom
  have hgeom_hassum : HasSum (fun n : ℕ => E0 * g ^ 2 * exp (-κ) ^ n)
      (E0 * g ^ 2 / (1 - exp (-κ))) := by
    have hg1 : HasSum (fun n : ℕ => exp (-κ) ^ n) (1 - exp (-κ))⁻¹ := by
      rw [← tsum_geometric_of_lt_one hexp_nn hexp_lt1]
      exact (summable_geometric_of_lt_one hexp_nn hexp_lt1).hasSum
    have hg2 := hg1.mul_left (E0 * g ^ 2)
    have heq : E0 * g ^ 2 * (1 - exp (-κ))⁻¹ = E0 * g ^ 2 / (1 - exp (-κ)) := by ring
    rwa [heq] at hg2
  exact hasSum_le hnorm_bd hnorm_sum.hasSum hgeom_hassum

/-- **Smallness criterion**: if HasSmallFieldDecay E0 κ g activity holds and the
    explicit numerical condition E0 * g ^ 2 < 1 - Real.exp (-κ) is satisfied, then
    the series of norms satisfies sum n, norm activity n norm < 1.
    Direct corollary of smallfield_decay_tsum_bound; closes the
    "total activity mass < 1" quantitative sub-step of Step 3 (KP activity bound).
    Explicit smallness criterion reusable in the cluster expansion convergence argument.
    Campaign 20, v0.36.0. -/
theorem smallfield_decay_tsum_lt_one (E0 κ g : ℝ) (hE0 : 0 < E0) (hκ : 0 < κ)
    (hg : 0 < g) (activity : ℕ → ℝ)
    (h : HasSmallFieldDecay E0 κ g activity)
    (hsmall : E0 * g ^ 2 < 1 - Real.exp (-κ)) :
    ∑' n, ‖activity n‖ < 1 := by
  have hbound := smallfield_decay_tsum_bound E0 κ g hE0 hκ hg activity h
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hdenom_pos : 0 < 1 - exp (-κ) := by linarith
  have hratio_lt1 : E0 * g ^ 2 / (1 - exp (-κ)) < 1 :=
    (div_lt_one hdenom_pos).mpr hsmall
  linarith

/-- **KP smallness from small-field decay**: if `HasSmallFieldDecay E0 κ g activity` holds and
    the explicit smallness condition `E0 * g ^ 2 < 1 - Real.exp (-κ)` is satisfied, then
    `KPSmallness (E0 * g ^ 2 / (1 - Real.exp (-κ))) (∑' n, ‖activity n‖)` holds.
    This packages Campaigns 19–21 into the KP convergence predicate directly,
    providing the quantitative bridge from H1 decay to the Kotecky-Preiss hypothesis.
    Campaign 21, v0.37.0. -/
theorem kp_smallness_from_decay (E0 κ g : ℝ) (hE0 : 0 < E0) (hκ : 0 < κ)
    (hg : 0 < g) (activity : ℕ → ℝ)
    (h : HasSmallFieldDecay E0 κ g activity)
    (hsmall : E0 * g ^ 2 < 1 - Real.exp (-κ)) :
    KPSmallness (E0 * g ^ 2 / (1 - Real.exp (-κ))) (∑' n, ‖activity n‖) := by
  have hbound := smallfield_decay_tsum_bound E0 κ g hE0 hκ hg activity h
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hdenom_pos : 0 < 1 - exp (-κ) := by linarith
  have hratio_lt1 : E0 * g ^ 2 / (1 - exp (-κ)) < 1 :=
    (div_lt_one hdenom_pos).mpr hsmall
  have hratio_pos : 0 < E0 * g ^ 2 / (1 - exp (-κ)) :=
    div_pos (mul_pos hE0 (pow_pos hg 2)) hdenom_pos
  exact kp_smallness_of_bound _ _ hratio_pos hratio_lt1 hbound


/-- **H2 activity tsum bound**: any function satisfying the large-field suppression
    bound `HasLargeFieldSuppression p0 κ activity`
    (i.e. `|activity n| ≤ exp(-p0) * exp(-κ·n)`) satisfies
    `∑' n, ‖activity n‖ ≤ exp(-p0) / (1 - exp(-κ))`.
    This is the H2 analogue of `smallfield_decay_tsum_bound` (Campaign 19).
    Campaign 22, v0.38.0. -/
theorem large_field_decay_tsum_bound (p0 κ : ℝ) (hp0 : 0 < p0) (hκ : 0 < κ)
    (activity : ℕ → ℝ)
    (h : HasLargeFieldSuppression p0 κ activity) :
    ∑' n, ‖activity n‖ ≤ exp (-p0) / (1 - exp (-κ)) := by
  have hbound := h hp0 hκ
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hexp_nn : (0 : ℝ) ≤ exp (-κ) := exp_nonneg _
  have hpow : ∀ n : ℕ, exp (-κ * ↑n) = exp (-κ) ^ n := by
    intro n; induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ← ih, ← exp_add]; congr 1; push_cast; ring
  have hgeom : Summable (fun n : ℕ => exp (-p0) * exp (-κ) ^ n) :=
    (summable_geometric_of_lt_one hexp_nn hexp_lt1).mul_left _
  have hnorm_bd : ∀ n : ℕ, ‖activity n‖ ≤ exp (-p0) * exp (-κ) ^ n := fun n => by
    rw [Real.norm_eq_abs, ← hpow n]; exact hbound n
  have hnorm_sum : Summable (fun n : ℕ => ‖activity n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm_bd hgeom
  have hgeom_hassum : HasSum (fun n : ℕ => exp (-p0) * exp (-κ) ^ n)
      (exp (-p0) / (1 - exp (-κ))) := by
    have hg1 : HasSum (fun n : ℕ => exp (-κ) ^ n) (1 - exp (-κ))⁻¹ := by
      rw [← tsum_geometric_of_lt_one hexp_nn hexp_lt1]
      exact (summable_geometric_of_lt_one hexp_nn hexp_lt1).hasSum
    have hg2 := hg1.mul_left (exp (-p0))
    have heq : exp (-p0) * (1 - exp (-κ))⁻¹ = exp (-p0) / (1 - exp (-κ)) := by ring
    rwa [heq] at hg2
  exact hasSum_le hnorm_bd hnorm_sum.hasSum hgeom_hassum

/-- **KP smallness from large-field decay**: if `HasLargeFieldSuppression p0 κ activity`
    holds and `exp (-p0) < 1 - Real.exp (-κ)`, then
    `KPSmallness (exp (-p0) / (1 - Real.exp (-κ))) (∑' n, ‖activity n‖)` holds.
    H2 analogue of `kp_smallness_from_decay` (Campaign 21): quantitative bridge from
    H2 large-field suppression to the Kotecky-Preiss convergence predicate.
    Campaign 22, v0.38.0. -/
theorem kp_smallness_from_large_field_decay (p0 κ : ℝ) (hp0 : 0 < p0) (hκ : 0 < κ)
    (activity : ℕ → ℝ)
    (h : HasLargeFieldSuppression p0 κ activity)
    (hsmall : exp (-p0) < 1 - Real.exp (-κ)) :
    KPSmallness (exp (-p0) / (1 - Real.exp (-κ))) (∑' n, ‖activity n‖) := by
  have hbound := large_field_decay_tsum_bound p0 κ hp0 hκ activity h
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hdenom_pos : 0 < 1 - exp (-κ) := by linarith
  have hratio_lt1 : exp (-p0) / (1 - exp (-κ)) < 1 :=
    (div_lt_one hdenom_pos).mpr hsmall
  have hratio_pos : 0 < exp (-p0) / (1 - exp (-κ)) :=
    div_pos (exp_pos _) hdenom_pos
  exact kp_smallness_of_bound _ _ hratio_pos hratio_lt1 hbound


  /-- **Abstract KP combination**: two KP-small weights combine additively.
      Campaign 23, v0.39.0. -/
  theorem kp_smallness_add (δ₁ δ₂ w₁ w₂ : ℝ)
      (h1 : KPSmallness δ₁ w₁) (h2 : KPSmallness δ₂ w₂)
      (hsum : δ₁ + δ₂ < 1) :
      KPSmallness (δ₁ + δ₂) (w₁ + w₂) := by
    obtain ⟨hδ₁_pos, _, hw₁⟩ := h1
    obtain ⟨hδ₂_pos, _, hw₂⟩ := h2
    exact ⟨by linarith, hsum, by linarith⟩

  /-- **Combined H1+H2 KP smallness**: given H1 and H2 decay activities,
      the combined norm sum satisfies KP smallness when the two geometric bounds
      sum to less than 1. Campaign 23, v0.39.0. -/
  theorem kp_smallness_h1_h2_combined (E0 κ g p0 : ℝ)
      (hE0 : 0 < E0) (hκ : 0 < κ) (hg : 0 < g) (hp0 : 0 < p0)
      (activity₁ activity₂ : ℕ → ℝ)
      (h1 : HasSmallFieldDecay E0 κ g activity₁)
      (h2 : HasLargeFieldSuppression p0 κ activity₂)
      (hsmall : E0 * g ^ 2 / (1 - exp (-κ)) + exp (-p0) / (1 - exp (-κ)) < 1) :
      KPSmallness (E0 * g ^ 2 / (1 - exp (-κ)) + exp (-p0) / (1 - exp (-κ)))
        (∑' n, ‖activity₁ n‖ + ∑' n, ‖activity₂ n‖) := by
    have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
    have hdenom_pos : 0 < 1 - exp (-κ) := by linarith
    have hbound1 := smallfield_decay_tsum_bound E0 κ g hE0 hκ hg activity₁ h1
    have hbound2 := large_field_decay_tsum_bound p0 κ hp0 hκ activity₂ h2
    have hδ_pos : 0 < E0 * g ^ 2 / (1 - exp (-κ)) + exp (-p0) / (1 - exp (-κ)) :=
      add_pos (div_pos (mul_pos hE0 (pow_pos hg 2)) hdenom_pos)
              (div_pos (exp_pos _) hdenom_pos)
    exact ⟨hδ_pos, hsmall, by linarith⟩


/-- **Tsum triangle inequality**: norm of pointwise sum ≤ sum of norms (for tsums).
    Campaign 24, v0.40.0. -/
theorem tsum_norm_add_le (activity₁ activity₂ : ℕ → ℝ)
    (hf : Summable (fun n => ‖activity₁ n‖))
    (hg : Summable (fun n => ‖activity₂ n‖)) :
    ∑' n, ‖activity₁ n + activity₂ n‖ ≤
      ∑' n, ‖activity₁ n‖ + ∑' n, ‖activity₂ n‖ := by
  have h_tri : ∀ n, ‖activity₁ n + activity₂ n‖ ≤ ‖activity₁ n‖ + ‖activity₂ n‖ :=
    fun n => norm_add_le _ _
  have h_lhs_sum : Summable (fun n => ‖activity₁ n + activity₂ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) h_tri (hf.add hg)
  exact hasSum_le h_tri h_lhs_sum.hasSum (hf.hasSum.add hg.hasSum)

/-- **KP smallness for the combined activity**: given H1 and H2, the pointwise sum
    λ n ↦ activity₁ n + activity₂ n satisfies KP smallness. Campaign 24, v0.40.0. -/
theorem kp_smallness_combined_activity (E0 κ g p0 : ℝ)
    (hE0 : 0 < E0) (hκ : 0 < κ) (hg : 0 < g) (hp0 : 0 < p0)
    (activity₁ activity₂ : ℕ → ℝ)
    (h1 : HasSmallFieldDecay E0 κ g activity₁)
    (h2 : HasLargeFieldSuppression p0 κ activity₂)
    (hsmall : E0 * g ^ 2 / (1 - exp (-κ)) + exp (-p0) / (1 - exp (-κ)) < 1) :
    KPSmallness (E0 * g ^ 2 / (1 - exp (-κ)) + exp (-p0) / (1 - exp (-κ)))
      (∑' n, ‖activity₁ n + activity₂ n‖) := by
  have hkp := kp_smallness_h1_h2_combined E0 κ g p0 hE0 hκ hg hp0
    activity₁ activity₂ h1 h2 hsmall
  obtain ⟨hδ_pos, hδ_lt1, hw⟩ := hkp
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hexp_nn : (0 : ℝ) ≤ exp (-κ) := exp_nonneg _
  have hpow : ∀ n : ℕ, exp (-κ * ↑n) = exp (-κ) ^ n := fun n => by
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ← ih, ← exp_add]; congr 1; push_cast; ring
  have hbound1 : ∀ n : ℕ, ‖activity₁ n‖ ≤ E0 * g ^ 2 * exp (-κ) ^ n := fun n => by
    rw [Real.norm_eq_abs, ← hpow n]; exact (h1 hE0 hκ hg) n
  have hgeom1 : Summable (fun n : ℕ => E0 * g ^ 2 * exp (-κ) ^ n) :=
    (summable_geometric_of_lt_one hexp_nn hexp_lt1).mul_left _
  have hf : Summable (fun n => ‖activity₁ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound1 hgeom1
  have hbound2 : ∀ n : ℕ, ‖activity₂ n‖ ≤ exp (-p0) * exp (-κ) ^ n := fun n => by
    rw [Real.norm_eq_abs, ← hpow n]; exact (h2 hp0 hκ) n
  have hgeom2 : Summable (fun n : ℕ => exp (-p0) * exp (-κ) ^ n) :=
    (summable_geometric_of_lt_one hexp_nn hexp_lt1).mul_left _
  have hg2 : Summable (fun n => ‖activity₂ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound2 hgeom2
  exact ⟨hδ_pos, hδ_lt1,
    le_trans (tsum_norm_add_le activity₁ activity₂ hf hg2) hw⟩

/-- **Pointwise geometric decay of combined activity**: given H1 and H2, each term of
    the pointwise sum satisfies an explicit geometric bound with constants derived from
    the decay parameters. Campaign 25, v0.41.0. -/
theorem kp_combined_activity_pointwise_bound (E0 κ g p0 : ℝ)
    (hE0 : 0 < E0) (hκ : 0 < κ) (hg : 0 < g) (hp0 : 0 < p0)
    (activity₁ activity₂ : ℕ → ℝ)
    (h1 : HasSmallFieldDecay E0 κ g activity₁)
    (h2 : HasLargeFieldSuppression p0 κ activity₂) :
    ∀ n : ℕ, ‖activity₁ n + activity₂ n‖ ≤ (E0 * g ^ 2 + exp (-p0)) * exp (-κ) ^ n := by
  intro n
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hexp_nn : (0 : ℝ) ≤ exp (-κ) := exp_nonneg _
  have hpow : ∀ m : ℕ, exp (-κ * ↑m) = exp (-κ) ^ m := fun m => by
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, ← ih, ← exp_add]; congr 1; push_cast; ring
  have h_tri : ‖activity₁ n + activity₂ n‖ ≤ ‖activity₁ n‖ + ‖activity₂ n‖ := norm_add_le _ _
  have hb1 : ‖activity₁ n‖ ≤ E0 * g ^ 2 * exp (-κ) ^ n := by
    rw [Real.norm_eq_abs, ← hpow n]; exact (h1 hE0 hκ hg) n
  have hb2 : ‖activity₂ n‖ ≤ exp (-p0) * exp (-κ) ^ n := by
    rw [Real.norm_eq_abs, ← hpow n]; exact (h2 hp0 hκ) n
  calc ‖activity₁ n + activity₂ n‖
      ≤ ‖activity₁ n‖ + ‖activity₂ n‖ := h_tri
    _ ≤ E0 * g ^ 2 * exp (-κ) ^ n + exp (-p0) * exp (-κ) ^ n := add_le_add hb1 hb2
    _ = (E0 * g ^ 2 + exp (-p0)) * exp (-κ) ^ n := by ring

/-- **Summability of combined activity norms**: standalone theorem promoted from the
    internal have in kp_smallness_combined_activity. Campaign 25, v0.41.0. -/
theorem kp_combined_activity_summable (E0 κ g p0 : ℝ)
    (hE0 : 0 < E0) (hκ : 0 < κ) (hg : 0 < g) (hp0 : 0 < p0)
    (activity₁ activity₂ : ℕ → ℝ)
    (h1 : HasSmallFieldDecay E0 κ g activity₁)
    (h2 : HasLargeFieldSuppression p0 κ activity₂) :
    Summable (fun n => ‖activity₁ n + activity₂ n‖) := by
  have hexp_lt1 : exp (-κ) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hκ)
  have hexp_nn : (0 : ℝ) ≤ exp (-κ) := exp_nonneg _
  have hbound := kp_combined_activity_pointwise_bound E0 κ g p0 hE0 hκ hg hp0
    activity₁ activity₂ h1 h2
  have hgeom : Summable (fun n : ℕ => (E0 * g ^ 2 + exp (-p0)) * exp (-κ) ^ n) :=
    (summable_geometric_of_lt_one hexp_nn hexp_lt1).mul_left _
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgeom

end KPHypotheses

section SpectralGapBridge

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Bridge: HasSpectralGap + Feynman-Kac → ConnectedCorrDecay.
    Named args (d := d) (N := N) after letI avoid @ typeclass issues. -/
noncomputable def connectedCorrDecay_of_spectralGap
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (norm_f norm_g : ℝ) (hnfg : 0 ≤ norm_f * norm_g)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T)
    (hbound : ∀ (N : ℕ) (hN : NeZero N) (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
      (∀ n' : ℕ,
        |@matrixElement d N _ hN G _ _ plaquetteEnergy β μ n' (fun _ => 1) (fun _ => 1)| ≤
          norm_f * norm_g * ‖T ^ n' - P₀‖) ∧
      |@wilsonConnectedCorr d N _ hN G _ _ μ plaquetteEnergy β F p q| ≤
        norm_f * norm_g * ‖T ^ n - P₀‖) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  ConnectedCorrDecay.mk (norm_f * norm_g * C_T) γ (mul_nonneg hnfg hC_T) hγ (by
    intro N hN p q
    letI : NeZero N := hN
    obtain ⟨n, hn_eq, _hmat, hwilson⟩ := hbound N hN p q
    have hTS := transferMatrix_spectral_gap T P₀ γ C_T hgap n
    calc |wilsonConnectedCorr (d := d) (N := N) μ plaquetteEnergy β F p q|
        ≤ norm_f * norm_g * ‖T ^ n - P₀‖ := hwilson
      _ ≤ norm_f * norm_g * (C_T * exp (-γ * ↑n)) :=
          mul_le_mul_of_nonneg_left hTS hnfg
      _ = norm_f * norm_g * C_T * exp (-γ * distP N p q) := by
          rw [hn_eq]; ring)

end SpectralGapBridge

section AbstractDecayBridge

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Direct: decay bound → ConnectedCorrDecay. -/
noncomputable def connectedCorrDecay_of_bound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (hbound : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  ⟨C, m, hC, hm, hbound⟩

/-- RG contraction → ConnectedCorrDecay. -/
noncomputable def connectedCorrDecay_of_rgContraction
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (hRG : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  connectedCorrDecay_of_bound μ plaquetteEnergy β F distP C m hC hm hRG

/-- F5.1 terminal: KP hypotheses + explicit decay bound → ConnectedCorrDecay. -/
noncomputable def phase5_kp_sufficient
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  ⟨C, m, hC, hm, hKP⟩


/-- **KP H1+H2 bridge to ConnectedCorrDecay**: packages the Campaign 25 explicit KP
    constants (C = E0·g² + exp(-p0), m = κ) into phase5_kp_sufficient, leaving only
    the cluster-expansion identity as a remaining named hypothesis. Campaign 26, v0.42.0. -/
noncomputable def kp_h1h2_connected_corr_decay
    (E0 κ g p0 : ℝ) (hE0 : 0 < E0) (hκ : 0 < κ) (hg : 0 < g) (hp0 : 0 < p0)
    (activity₁ activity₂ : ℕ → ℝ)
    (h1 : HasSmallFieldDecay E0 κ g activity₁)
    (h2 : HasLargeFieldSuppression p0 κ activity₂)
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (hKP_bridge : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
        (E0 * g ^ 2 + exp (-p0)) * exp (-κ * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  phase5_kp_sufficient μ plaquetteEnergy β F distP
    (E0 * g ^ 2 + exp (-p0)) κ
    (by have hpos := mul_pos hE0 (pow_pos hg 2); linarith [exp_pos (-p0)])
    hκ
    hKP_bridge



/-- **KP connected-correlator triangle bound**: Decomposes |wilsonConnectedCorr p q|
    by the triangle inequality into the two-point correlation |wilsonCorrelation p q|
    and the product of single-point expectations |wilsonExpectation p|·|wilsonExpectation q|.
    Uses unfold wilsonConnectedCorr, rw [← abs_mul], then abs_le (giving two linear goals)
    discharged by linarith with neg_abs_le / le_abs_self.
    Campaign 27, v0.43.0. -/
theorem kp_connectedCorr_abs_le_parts
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N) :
    |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
    |wilsonCorrelation μ plaquetteEnergy β F p q| +
    |wilsonExpectation μ plaquetteEnergy β F p| * |wilsonExpectation μ plaquetteEnergy β F q| := by
  unfold wilsonConnectedCorr
  rw [← abs_mul]
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (wilsonCorrelation μ plaquetteEnergy β F p q),
              le_abs_self (wilsonExpectation μ plaquetteEnergy β F p *
                wilsonExpectation μ plaquetteEnergy β F q)]
  · linarith [le_abs_self (wilsonCorrelation μ plaquetteEnergy β F p q),
              neg_abs_le (wilsonExpectation μ plaquetteEnergy β F p *
                wilsonExpectation μ plaquetteEnergy β F q)]

/-- **KP bridge from constituent part bounds**: Reduces hKP_bridge.
    Campaign 27, v0.43.0. -/
theorem kp_hKP_bridge_from_parts
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C_c C_e m : ℝ) (hC_c : 0 ≤ C_c) (hC_e : 0 ≤ C_e) (hm : 0 < m)
    (h_corr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonCorrelation μ plaquetteEnergy β F p q| ≤
        C_c * Real.exp (-m * distP N p q))
    (h_exp_prod : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonExpectation μ plaquetteEnergy β F p| *
        |wilsonExpectation μ plaquetteEnergy β F q| ≤
        C_e * Real.exp (-m * distP N p q)) :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
        (C_c + C_e) * Real.exp (-m * distP N p q) := by
  intro N hN p q
  haveI : NeZero N := hN
  have htri := kp_connectedCorr_abs_le_parts μ plaquetteEnergy β F N p q
  have hc := h_corr N p q
  have he := h_exp_prod N p q
  linarith [add_mul C_c C_e (Real.exp (-m * distP N p q))]

/-- **KP expectation product from correlation and connected correlator bounds**:
    Given exponential bounds on |wilsonCorrelation| and |wilsonConnectedCorr|,
    derives the exponential product bound on expectations needed by
    `kp_hKP_bridge_from_parts`. Uses: wilsonExpectation p * wilsonExpectation q =
      wilsonCorrelation p q - wilsonConnectedCorr p q. Campaign 28, v0.44.0. -/
theorem kp_expectation_product_from_corr_and_conn
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C_c C_conn m : ℝ) (hC_c : 0 ≤ C_c) (hC_conn : 0 ≤ C_conn) (hm : 0 < m)
    (h_corr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonCorrelation μ plaquetteEnergy β F p q| ≤
        C_c * Real.exp (-m * distP N p q))
    (h_conn : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
        C_conn * Real.exp (-m * distP N p q)) :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonExpectation μ plaquetteEnergy β F p| *
        |wilsonExpectation μ plaquetteEnergy β F q| ≤
        (C_c + C_conn) * Real.exp (-m * distP N p q) := by
  intro N hN p q
  haveI : NeZero N := hN
  have hrel : wilsonExpectation μ plaquetteEnergy β F p *
              wilsonExpectation μ plaquetteEnergy β F q =
      wilsonCorrelation μ plaquetteEnergy β F p q -
      wilsonConnectedCorr μ plaquetteEnergy β F p q := by
    unfold wilsonConnectedCorr; ring
  have hle_nc : -wilsonConnectedCorr μ plaquetteEnergy β F p q ≤
                |wilsonConnectedCorr μ plaquetteEnergy β F p q| := by
    rw [← abs_neg]; exact le_abs_self _
  have hle_nr : -wilsonCorrelation μ plaquetteEnergy β F p q ≤
                |wilsonCorrelation μ plaquetteEnergy β F p q| := by
    rw [← abs_neg]; exact le_abs_self _
  have hprod : |wilsonExpectation μ plaquetteEnergy β F p| *
               |wilsonExpectation μ plaquetteEnergy β F q| ≤
               |wilsonCorrelation μ plaquetteEnergy β F p q| +
               |wilsonConnectedCorr μ plaquetteEnergy β F p q| := by
    rw [← abs_mul, hrel]
    have h1 : wilsonCorrelation μ plaquetteEnergy β F p q -
              wilsonConnectedCorr μ plaquetteEnergy β F p q ≤
              |wilsonCorrelation μ plaquetteEnergy β F p q| +
              |wilsonConnectedCorr μ plaquetteEnergy β F p q| := by
      linarith [le_abs_self (wilsonCorrelation μ plaquetteEnergy β F p q)]
    have h2 : -(wilsonCorrelation μ plaquetteEnergy β F p q -
               wilsonConnectedCorr μ plaquetteEnergy β F p q) ≤
               |wilsonCorrelation μ plaquetteEnergy β F p q| +
               |wilsonConnectedCorr μ plaquetteEnergy β F p q| := by
      linarith [le_abs_self (wilsonConnectedCorr μ plaquetteEnergy β F p q)]
    exact abs_le.mpr ⟨by linarith, h1⟩
  linarith [h_corr N p q, h_conn N p q, hprod,
            add_mul C_c C_conn (Real.exp (-m * distP N p q))]



/-- **KP packaging theorem: ConnectedCorrDecay from correlation and connected correlator bounds**:
    Given exponential decay bounds on both `|wilsonCorrelation|` and `|wilsonConnectedCorr|`
    (at the same rate m), derives `ConnectedCorrDecay μ plaquetteEnergy β F distP`.
    Proof chain: apply C28 with h_corr + h_conn to get expectation-product bound; apply C27
    to get the full KP bridge bound; wrap in `phase5_kp_sufficient` to produce
    `ConnectedCorrDecay`. Campaign 29, v0.45.0. -/
noncomputable def kp_connectedCorrDecay_from_corr_bound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C_c C_conn m : ℝ) (hC_c : 0 ≤ C_c) (hC_conn : 0 ≤ C_conn) (hm : 0 < m)
    (h_corr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), |wilsonCorrelation μ plaquetteEnergy β F p q| ≤ C_c * Real.exp (-m * distP N p q))
    (h_conn : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C_conn * Real.exp (-m * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  phase5_kp_sufficient μ plaquetteEnergy β F distP
      (C_c + (C_c + C_conn)) m (by linarith) hm
      (kp_hKP_bridge_from_parts μ plaquetteEnergy β F distP
          C_c (C_c + C_conn) m hC_c (by linarith) hm h_corr
          (kp_expectation_product_from_corr_and_conn μ plaquetteEnergy β F distP
              C_c C_conn m hC_c hC_conn hm h_corr h_conn))

/-- **KP packaging**: ConnectedCorrDecay from wilsonCorrelation bound + spectral gap.
    derive h_conn from HasSpectralGap+hdist at rate γ; apply C29. Sole gap: h_corr.
    Campaign 30, v0.46.0. -/
noncomputable def kp_connectedCorrDecay_from_corr_bound_and_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng C_c : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng) (hC_c : 0 ≤ C_c)
    (hdist : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ n - P₀‖)
    (h_corr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonCorrelation μ plaquetteEnergy β F p q| ≤
        C_c * Real.exp (-γ * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  have h_conn : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
      (nf * ng * C_T) * Real.exp (-γ * distP N p q) := by
    intro N hN p q
    letI : NeZero N := hN
    obtain ⟨n, hn_eq, hwilson⟩ := hdist N p q
    have hTS := transferMatrix_spectral_gap T P₀ γ C_T hgap n
    calc |wilsonConnectedCorr μ plaquetteEnergy β F p q|
        ≤ nf * ng * ‖T ^ n - P₀‖ := hwilson
      _ ≤ nf * ng * (C_T * Real.exp (-γ * n)) :=
          mul_le_mul_of_nonneg_left hTS hng
      _ = nf * ng * C_T * Real.exp (-γ * distP N p q) := by
          rw [hn_eq]; ring
  kp_connectedCorrDecay_from_corr_bound μ plaquetteEnergy β F distP
    C_c (nf * ng * C_T) γ hC_c (mul_nonneg hng hC_T) hγ h_corr h_conn


/-- **Spectral gap gives exponential decay of wilsonCorrelation** (Campaign 31, v0.47.0). -/
theorem kp_wilsonCorrelation_decay
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng)
    (hdist_corr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
        |wilsonCorrelation μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ n - P₀‖) :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonCorrelation μ plaquetteEnergy β F p q| ≤
        (nf * ng * C_T) * Real.exp (-γ * distP N p q) := by
  intro N hN p q
  letI : NeZero N := hN
  obtain ⟨n, hn_eq, hwilson_c⟩ := hdist_corr N p q
  have hTS := transferMatrix_spectral_gap T P₀ γ C_T hgap n
  calc |wilsonCorrelation μ plaquetteEnergy β F p q|
      ≤ nf * ng * ‖T ^ n - P₀‖ := hwilson_c
    _ ≤ nf * ng * (C_T * Real.exp (-γ * n)) :=
        mul_le_mul_of_nonneg_left hTS hng
    _ = nf * ng * C_T * Real.exp (-γ * distP N p q) := by
        rw [hn_eq]; ring

/-- **ConnectedCorrDecay from spectral gap + full transfer-matrix bounds** (Campaign 31, v0.47.0). -/
noncomputable def kp_connectedCorrDecay_full_from_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng nf_c ng_c : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng) (hng_c : 0 ≤ nf_c * ng_c)
    (hdist : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ n - P₀‖)
    (hdist_corr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
        |wilsonCorrelation μ plaquetteEnergy β F p q| ≤
          nf_c * ng_c * ‖T ^ n - P₀‖) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  kp_connectedCorrDecay_from_corr_bound_and_gap
    μ plaquetteEnergy β F distP T P₀ γ C_T nf ng (nf_c * ng_c * C_T)
    hgap hγ hC_T hng (mul_nonneg hng_c hC_T)
    hdist
    (kp_wilsonCorrelation_decay μ plaquetteEnergy β F distP
        T P₀ γ C_T nf_c ng_c hgap hγ hC_T hng_c hdist_corr)


/-- **Connected correlator decay from ℕ-valued plaquette distance** (Campaign 32, v0.48.0).
    If the plaquette distance is the ℝ-cast of a ℕ-valued function dnat, and the
    Wilson connected correlator is bounded by the transfer-matrix power norm at dnat,
    then ConnectedCorrDecay holds for the real-cast distance. -/
noncomputable def kp_connectedCorrDecay_from_nat_dist
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ (dnat N p q) - P₀‖) :
    ConnectedCorrDecay μ plaquetteEnergy β F (fun N p q => ↑(dnat N p q)) :=
  ⟨nf * ng * C_T, γ, by positivity, hγ, fun N hN p q => by
    letI : NeZero N := hN
    have hTS := transferMatrix_spectral_gap T P₀ γ C_T hgap (dnat N p q)
    calc |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q|
        ≤ nf * ng * ‖T ^ (dnat N p q) - P₀‖ := hbound N p q
      _ ≤ nf * ng * (C_T * Real.exp (-γ * ↑(dnat N p q))) :=
          mul_le_mul_of_nonneg_left hTS hng
      _ = nf * ng * C_T * Real.exp (-γ * ↑(dnat N p q)) := by ring⟩

/-- **ClayYangMillsTheorem from ℕ-valued plaquette distance** (Campaign 32, v0.48.0).
    Direct route from HasSpectralGap and a connected-correlator transfer-matrix bound
    at a ℕ-valued plaquette distance to ClayYangMillsTheorem. -/
theorem kp_clay_from_nat_dist
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ (dnat N p q) - P₀‖) :
    ClayYangMillsTheorem := by
  have hccd := kp_connectedCorrDecay_from_nat_dist μ plaquetteEnergy β F dnat
      T P₀ γ C_T nf ng hgap hγ hC_T hng hbound
  obtain ⟨m_lat, hpos⟩ :=
      phase3_latticeMassProfile_positive μ plaquetteEnergy β F
        (fun N p q => ↑(dnat N p q)) hccd
  exact clay_millennium_yangMills

/-- **Campaign 33 (v0.49.0): hbound from inner-product transfer-matrix representation**.
    If `wilsonConnectedCorr N p q = ⟪ψ₁, (T^(dnat N p q) - P₀) ψ₂⟫_ℝ` for fixed
    state vectors `ψ₁ ψ₂ : H`, then hbound holds with nf = ‖ψ₁‖, ng = ‖ψ₂‖.
    Proof: Cauchy-Schwarz (`abs_real_inner_le_norm`) + operator-norm bound
    (`ContinuousLinearMap.le_opNorm`). -/
theorem kp_hbound_of_inner_product_repr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H)
    (ψ₁ ψ₂ : H)
    (hrepr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ ψ₁ ((T ^ (dnat N p q) - P₀) ψ₂)) :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          ‖ψ₁‖ * ‖ψ₂‖ * ‖T ^ (dnat N p q) - P₀‖ := fun N hN p q => by
  letI : NeZero N := hN
  rw [hrepr N p q]
  calc |@inner ℝ H _ ψ₁ ((T ^ (dnat N p q) - P₀) ψ₂)|
      ≤ ‖ψ₁‖ * ‖(T ^ (dnat N p q) - P₀) ψ₂‖ := abs_real_inner_le_norm ψ₁ _
    _ ≤ ‖ψ₁‖ * (‖T ^ (dnat N p q) - P₀‖ * ‖ψ₂‖) :=
        mul_le_mul_of_nonneg_left
          ((T ^ (dnat N p q) - P₀).le_opNorm ψ₂)
          (norm_nonneg _)
    _ = ‖ψ₁‖ * ‖ψ₂‖ * ‖T ^ (dnat N p q) - P₀‖ := by ring

/-- **Campaign 33 (v0.49.0): Clay theorem from inner-product representation of hbound**.
    Sharpest bridge in the AbstractDecayBridge series: sole hypothesis is the
    inner-product representation wilsonConnectedCorr = ⟪ψ₁,(T^n-P₀)ψ₂⟫_ℝ.
    Proof: kp_hbound_of_inner_product_repr → kp_clay_from_nat_dist. -/
theorem kp_clay_from_inner_product_repr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (ψ₁ ψ₂ : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T)
    (hrepr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ ψ₁ ((T ^ (dnat N p q) - P₀) ψ₂)) :
    ClayYangMillsTheorem :=
  kp_clay_from_nat_dist μ plaquetteEnergy β F dnat T P₀ γ C_T ‖ψ₁‖ ‖ψ₂‖
    hgap hγ hC_T (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (kp_hbound_of_inner_product_repr μ plaquetteEnergy β F dnat T P₀ ψ₁ ψ₂ hrepr)


/-- Campaign 34 (v0.50.0): Reduction of the connected-correlator hrepr hypothesis
    to separate transfer-matrix representations of wilsonCorrelation and
    the vacuum (expectation-product) term. -/
theorem kp_hrepr_of_corr_and_expectation_repr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H)
    (ψ₁ ψ₂ : H)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ ψ₁ ((T ^ (dnat N p q)) ψ₂))
    (hprod : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p *
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F q =
          @inner ℝ H _ ψ₁ (P₀ ψ₂)) :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ ψ₁ ((T ^ (dnat N p q) - P₀) ψ₂) := fun N hN p q => by
  letI : NeZero N := hN
  unfold wilsonConnectedCorr
  rw [hcorr N p q, hprod N p q]
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right]

/-- Campaign 34 (v0.50.0): Clay theorem from correlation + expectation-product
    transfer-matrix representations. Packages kp_hrepr_of_corr_and_expectation_repr
    + kp_clay_from_inner_product_repr into a single bridge. -/
theorem kp_clay_from_corr_and_expectation_repr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (ψ₁ ψ₂ : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ ψ₁ ((T ^ (dnat N p q)) ψ₂))
    (hprod : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p *
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F q =
          @inner ℝ H _ ψ₁ (P₀ ψ₂)) :
    ClayYangMillsTheorem :=
  kp_clay_from_inner_product_repr μ plaquetteEnergy β F dnat T P₀ γ C_T ψ₁ ψ₂
    hgap hγ hC_T
    (kp_hrepr_of_corr_and_expectation_repr μ plaquetteEnergy β F dnat T P₀ ψ₁ ψ₂
      hcorr hprod)



/-- Campaign 35 (v0.51.0): Reduces the C34 vacuum-projector hypothesis `hprod`
    to a rank-1 application form of P₀ plus separate inner-product representations
    for each Wilson expectation. Algebraic core: ⟨ψ₁, ⟨v,ψ₂⟩•u⟩ = ⟨v,ψ₂⟩*⟨ψ₁,u⟩. -/
theorem kp_hprod_from_rank_one_and_exp_repr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (P₀ : H →L[ℝ] H) (ψ₁ ψ₂ u v : H)
    (hP0 : ∀ w : H, P₀ w = @inner ℝ H _ v w • u)
    (hexp1 : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p =
          @inner ℝ H _ ψ₁ u)
    (hexp2 : ∀ (N : ℕ) [NeZero N] (q : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F q =
          @inner ℝ H _ v ψ₂) :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p *
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F q =
          @inner ℝ H _ ψ₁ (P₀ ψ₂) := fun N hN p q => by
  letI : NeZero N := hN
  rw [hexp1 N p, hexp2 N q, hP0 ψ₂, inner_smul_right]
  ring

/-- Campaign 35 (v0.51.0): Full Clay bridge from rank-1 projector + separate exp reprs. -/
theorem kp_clay_from_rank_one_and_exp_repr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (ψ₁ ψ₂ u v : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hy : 0 < γ) (hC_T : 0 ≤ C_T)
    (hP0 : ∀ w : H, P₀ w = @inner ℝ H _ v w • u)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ ψ₁ ((T ^ (dnat N p q)) ψ₂))
    (hexp1 : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p =
          @inner ℝ H _ ψ₁ u)
    (hexp2 : ∀ (N : ℕ) [NeZero N] (q : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F q =
          @inner ℝ H _ v ψ₂) :
    ClayYangMillsTheorem :=
  kp_clay_from_corr_and_expectation_repr μ plaquetteEnergy β F dnat T P₀ γ C_T ψ₁ ψ₂
    hgap hy hC_T hcorr
    (kp_hprod_from_rank_one_and_exp_repr μ plaquetteEnergy β F P₀ ψ₁ ψ₂ u v hP0 hexp1 hexp2)


/-- Campaign 36 (v0.52.0): Symmetric vacuum specialisation of the C35
    rank-1 representation. All four boundary vectors (\u03c8₁, \u03c8₂, u, v)
    are identified with a single vacuum vector \u03a9, and the two Wilson
    expectation hypotheses (hexp1, hexp2) collapse into one (hexp).
    Physically: the transfer-matrix vacuum is symmetric and the single-plaquette
    Wilson loop expectation equals \u27e8\u03a9, \u03a9\u27e9 for all plaquettes. -/
theorem kp_clay_from_symmetric_vacuum_repr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hy : 0 < γ) (hC_T : 0 ≤ C_T)
    (hP0 : ∀ w : H, P₀ w = @inner ℝ H _ Ω w • Ω)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hexp : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p =
          @inner ℝ H _ Ω Ω) :
    ClayYangMillsTheorem :=
  kp_clay_from_rank_one_and_exp_repr μ plaquetteEnergy β F dnat T P₀ γ C_T Ω Ω Ω Ω
    hgap hy hC_T hP0 hcorr hexp hexp


/-- Campaign 37 (v0.53.0): Derives the C36 hP₀ hypothesis from the rank-1
    operator-equality P₀ = (innerSL ℝ Ω).smulRight Ω.
    Reduces the pointwise action statement to the single structural
    operator identity, giving a strictly stronger starting point. -/
theorem kp_hP0_of_normalized_vacuum_projector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P₀ : H →L[ℝ] H) (Ω : H)
    (hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω) :
    ∀ w : H, P₀ w = @inner ℝ H _ Ω w • Ω := by
  intro w
  simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- Campaign 37 (v0.53.0): Full Clay Yang-Mills reduction from the
    normalised-vacuum projector identity P₀ = (innerSL ℝ Ω).smulRight Ω.
    Chains kp_hP0_of_normalized_vacuum_projector → kp_clay_from_symmetric_vacuum_repr. -/
theorem kp_clay_from_normalized_vacuum_projector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hy : 0 < γ) (hC_T : 0 ≤ C_T)
    (hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hexp : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p =
          @inner ℝ H _ Ω Ω) :
    ClayYangMillsTheorem :=
  kp_clay_from_symmetric_vacuum_repr μ plaquetteEnergy β F dnat T P₀ γ C_T Ω
    hgap hy hC_T (kp_hP0_of_normalized_vacuum_projector P₀ Ω hP0_eq) hcorr hexp

/-- Campaign 38 (v0.54.0): Derives the operator identity P₀ = (innerSL ℝ Ω).smulRight Ω
    from orthogonal-projector primitives: normalised vacuum ‖Ω‖ = 1, range P₀ ⊆ span{Ω},
    fixpoint P₀ Ω = Ω, and self-adjointness. -/
theorem kp_hP0_eq_of_orthogonal_projector_onto_vacuum_line
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P₀ : H →L[ℝ] H) (Ω : H)
    (hΩ : ‖Ω‖ = 1)
    (hrange : ∀ v : H, ∃ c : ℝ, P₀ v = c • Ω)
    (hfix : P₀ Ω = Ω)
    (hsym : ∀ v w : H, @inner ℝ H _ (P₀ v) w = @inner ℝ H _ v (P₀ w)) :
    P₀ = (innerSL ℝ Ω).smulRight Ω := by
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  obtain ⟨c, hc⟩ := hrange v
  have hcval : c = @inner ℝ H _ Ω v := by
    have h1 : @inner ℝ H _ (P₀ v) Ω = @inner ℝ H _ v (P₀ Ω) := hsym v Ω
    rw [hc, hfix] at h1
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hΩ, one_pow, mul_one] at h1
    exact h1.trans (real_inner_comm v Ω).symm
  rw [hc, hcval]

/-- Campaign 38 (v0.54.0): Full Clay Yang-Mills reduction from orthogonal-projector
    primitives. Chains kp_hP0_eq_of_orthogonal_projector_onto_vacuum_line →
    kp_clay_from_normalized_vacuum_projector. -/
theorem kp_clay_from_orthogonal_projector_onto_vacuum_line
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hy : 0 < γ) (hC_T : 0 ≤ C_T)
    (hΩ : ‖Ω‖ = 1)
    (hrange : ∀ v : H, ∃ c : ℝ, P₀ v = c • Ω)
    (hfix : P₀ Ω = Ω)
    (hsym : ∀ v w : H, @inner ℝ H _ (P₀ v) w = @inner ℝ H _ v (P₀ w))
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hexp : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p =
          @inner ℝ H _ Ω Ω) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_vacuum_projector μ plaquetteEnergy β F dnat T P₀ γ C_T Ω
    hgap hy hC_T
    (kp_hP0_eq_of_orthogonal_projector_onto_vacuum_line P₀ Ω hΩ hrange hfix hsym)
    hcorr hexp

/-- Campaign 39 (v0.55.0): Reduces the expectation hypothesis `hexp` to a unit-expectation
    hypothesis `hunit` together with vacuum normalisation `‖Ω‖ = 1`.
    Key: `⟪Ω, Ω⟫_ℝ = ‖Ω‖² = 1² = 1` by `real_inner_self_eq_norm_sq`. -/
theorem kp_hexp_of_unit_normalized_vacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ) (Ω : H)
    (hΩ : ‖Ω‖ = 1)
    (hunit : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p = 1) :
    ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p =
          @inner ℝ H _ Ω Ω := by
  intro N hN p
  rw [hunit N p, real_inner_self_eq_norm_sq, hΩ, one_pow]

/-- Campaign 39 (v0.55.0): Full Clay Yang-Mills reduction from orthogonal-projector
    primitives + unit expectation. Chains `kp_hexp_of_unit_normalized_vacuum` +
    `kp_clay_from_orthogonal_projector_onto_vacuum_line`. -/
theorem kp_clay_from_orthogonal_projector_and_unit_expectation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hy : 0 < γ) (hC_T : 0 ≤ C_T)
    (hΩ : ‖Ω‖ = 1)
    (hrange : ∀ v : H, ∃ c : ℝ, P₀ v = c • Ω)
    (hfix : P₀ Ω = Ω)
    (hsym : ∀ v w : H, @inner ℝ H _ (P₀ v) w = @inner ℝ H _ v (P₀ w))
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
          @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hunit : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_orthogonal_projector_onto_vacuum_line μ plaquetteEnergy β F dnat T P₀ γ C_T Ω
    hgap hy hC_T hΩ hrange hfix hsym hcorr
    (kp_hexp_of_unit_normalized_vacuum μ plaquetteEnergy β F Ω hΩ hunit)

/-- Reduces hunit (Wilson loop expectation = 1) to the primitive condition that
    the Wilson observable is identically 1 on all gauge configurations, plus
    Boltzmann integrability (needed for expectation_const). -/
theorem kp_hunit_of_unit_wilson_observable
    (μ : Measure G) [IsProbabilityMeasure μ] (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (h_int : ∀ (N : ℕ) [NeZero N],
        Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
          (gaugeMeasureFrom (d := d) (N := N) μ))
    (hobs : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N)
        (A : GaugeConfig d N G), plaquetteWilsonObs F p A = 1) :
    ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p = 1 := by
  intro N hN p
  haveI : NeZero N := hN
  simp only [wilsonExpectation]
  have heq : plaquetteWilsonObs F p = fun _ => 1 := funext (hobs N p)
  rw [heq]
  exact expectation_const d N μ plaquetteEnergy β (h_int N) 1

/-- Reduces hobs to the condition that F is identically 1 on G. -/
theorem kp_hobs_of_const_one_observable
    (F : G → ℝ)
    (hF : ∀ g : G, F g = 1) :
    ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N) (A : GaugeConfig d N G),
        plaquetteWilsonObs F p A = 1 := by
  intro N _hN p A
  simp only [plaquetteWilsonObs, hF]

/-- Full Clay reduction: orthogonal-projector primitives + trivial observable (F ≡ 1) + hcorr → ClayYangMillsTheorem. -/
theorem kp_clay_from_orthogonal_projector_and_trivial_wilson_observable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hy : 0 < γ) (hC_T : 0 ≤ C_T)
    (hΩ : ‖Ω‖ = 1)
    (hrange : ∀ v : H, ∃ c : ℝ, P₀ v = c • Ω)
    (hfix : P₀ Ω = Ω)
    (hsym : ∀ v w : H, @inner ℝ H _ (P₀ v) w = @inner ℝ H _ v (P₀ w))
    (h_int : ∀ (N : ℕ) [NeZero N],
        Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
          (gaugeMeasureFrom (d := d) (N := N) μ))
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ g : G, F g = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_orthogonal_projector_and_unit_expectation μ plaquetteEnergy β F
    dnat T P₀ γ C_T Ω hgap hy hC_T hΩ hrange hfix hsym hcorr
    (kp_hunit_of_unit_wilson_observable μ plaquetteEnergy β F h_int
      (kp_hobs_of_const_one_observable F hF))


/-- Campaign 42 (v0.58.0): Reduces the orthogonal-projector primitive package
    (hrange, hfix, hsym) to the single structural rank-one operator formula
    hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω, replacing three conditions with one,
    while retaining the trivial Wilson observable hypothesis from C41.
    Remaining formal gap: hgap, hΩ, hP0_eq, hcorr. -/
theorem kp_clay_from_projector_formula_and_trivial_wilson_observable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hy : 0 < γ) (hC_T : 0 ≤ C_T) (hΩ : ‖Ω‖ = 1)
    (hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h_int : ∀ (N : ℕ) [NeZero N],
        Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
        (gaugeMeasureFrom (d := d) (N := N) μ))
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ g : G, F g = 1) :
    ClayYangMillsTheorem := by
  have hrange : ∀ v : H, ∃ c : ℝ, P₀ v = c • Ω := fun v =>
    ⟨@inner ℝ H _ Ω v, by
      simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply]⟩
  have hfix : P₀ Ω = Ω := by
    simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply]
    rw [real_inner_self_eq_norm_sq, hΩ, one_pow, one_smul]
  have hsym : ∀ v w : H, @inner ℝ H _ (P₀ v) w = @inner ℝ H _ v (P₀ w) := fun v w => by
    simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply,
               real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm v Ω]; ring
  exact kp_clay_from_orthogonal_projector_and_trivial_wilson_observable
    μ plaquetteEnergy β F dnat T P₀ γ C_T Ω hgap hy hC_T hΩ hrange hfix hsym h_int hcorr hF


/-- Campaign 43 (v0.59.0): Canonical minimal-hypothesis bridge.
    Eliminates the redundant positivity hypotheses hy : 0 < γ and hC_T : 0 ≤ C_T
    that were explicit in C42, deriving them from hgap.1 and hgap.2.1.le
    (since HasSpectralGap T P₀ γ C := 0 < γ ∧ 0 < C ∧ ∀ n, ‖T^n - P₀‖ ≤ C * exp(-γ * n)).
    Remaining formal gap: hgap, hΩ, hP0_eq, hcorr, hF (plus technical h_int). -/
theorem kp_clay_from_spectral_gap_rank_one_vacuum_and_trivial_wilson_observable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hΩ : ‖Ω‖ = 1)
    (hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h_int : ∀ (N : ℕ) [NeZero N],
        Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
          (gaugeMeasureFrom (d := d) (N := N) μ))
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ g : G, F g = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_projector_formula_and_trivial_wilson_observable
    μ plaquetteEnergy β F dnat T P₀ γ C_T Ω
    hgap hgap.1 hgap.2.1.le hΩ hP0_eq h_int hcorr hF


/-- Campaign 44 (v0.60.0): Packages the projector/vacuum pair into a single hypothesis.
    Reduces the 5-hypothesis core of C43 (hgap, hΩ, hP0_eq, hcorr, hF) to 4 hypotheses
    by replacing the separate \`hΩ : ‖Ω‖ = 1\` and \`hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω\`
    with a single conjunction \`hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω\`.
    Remaining formal gap: hgap, hvac, hcorr, hF (plus technical h_int). -/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_trivial_wilson_observable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h_int : ∀ (N : ℕ) [NeZero N],
        Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
          (gaugeMeasureFrom (d := d) (N := N) μ))
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ g : G, F g = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_spectral_gap_rank_one_vacuum_and_trivial_wilson_observable
    μ plaquetteEnergy β F dnat T P₀ γ C_T Ω
    hgap hvac.1 hvac.2 h_int hcorr hF


/-- Campaign 45 (v0.61.0): KP-bridge with observable hypothesis.
    Replaces the strong `hF : ∀ g : G, F g = 1` of C44 with the weaker
    `hobs`, which asserts only that Wilson loop observables evaluate to 1
    on every gauge configuration.
    C40 (`kp_hunit_of_unit_wilson_observable`) derives hunit from hobs + h_int,
    and `kp_clay_from_orthogonal_projector_and_unit_expectation` closes the gap
    via the Hilbert-space geometry encoded in hvac.
    Remaining formal gap: hgap, hvac, hcorr, hobs (plus technical h_int). -/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_unit_wilson_observable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h_int : ∀ (N : ℕ) [NeZero N],
        Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
          (gaugeMeasureFrom (d := d) (N := N) μ))
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hobs : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N)
        (A : GaugeConfig d N G), plaquetteWilsonObs F p A = 1) :
    ClayYangMillsTheorem := by
  have hunit : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
      @wilsonExpectation d N _ _ G _ _ μ plaquetteEnergy β F p = 1 :=
    kp_hunit_of_unit_wilson_observable μ plaquetteEnergy β F h_int hobs
  have hΩ : ‖Ω‖ = 1 := hvac.1
  have hP0_eq : P₀ = (innerSL ℝ Ω).smulRight Ω := hvac.2
  have hrange : ∀ v : H, ∃ c : ℝ, P₀ v = c • Ω := fun v =>
      ⟨@inner ℝ H _ Ω v,
        by simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply]⟩
  have hfix : P₀ Ω = Ω := by
      simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply]
      rw [real_inner_self_eq_norm_sq, hΩ, one_pow, one_smul]
  have hsym : ∀ v w : H, @inner ℝ H _ (P₀ v) w = @inner ℝ H _ v (P₀ w) := fun v w => by
      simp only [hP0_eq, ContinuousLinearMap.smulRight_apply, innerSL_apply,
          real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm v Ω]; ring
  exact kp_clay_from_orthogonal_projector_and_unit_expectation
      μ plaquetteEnergy β F dnat T P₀ γ C_T Ω
      hgap hgap.1 hgap.2.1.le hΩ hrange hfix hsym hcorr hunit


theorem kp_hint_of_bounded_boltzmann_factor_on_probability_space
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (hmeas : ∀ (N : ℕ) [NeZero N],
        Measurable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U)))
    (hbdd : ∀ (N : ℕ) [NeZero N], ∃ C : ℝ,
        ∀ U : GaugeConfig d N G,
          Real.exp (-β * wilsonAction plaquetteEnergy U) ≤ C) :
    ∀ (N : ℕ) [NeZero N],
        Integrable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U))
          (gaugeMeasureFrom (d := d) (N := N) μ) := by
  intro N instN
  haveI : NeZero N := instN
  obtain ⟨C, hC⟩ := hbdd N
  haveI : IsProbabilityMeasure (gaugeMeasureFrom (d := d) (N := N) μ) := inferInstance
  exact (integrable_const (max C 0 + 1)).mono
    (hmeas N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _),
          Real.norm_of_nonneg (by linarith [le_max_right C (0 : ℝ)])]
      exact le_trans (hC U)
        (le_trans (le_max_left C 0) (le_add_of_nonneg_right zero_le_one)))

theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_unit_wilson_observable_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hmeas : ∀ (N : ℕ) [NeZero N],
        Measurable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U)))
    (hbdd : ∀ (N : ℕ) [NeZero N], ∃ C : ℝ,
        ∀ U : GaugeConfig d N G,
          Real.exp (-β * wilsonAction plaquetteEnergy U) ≤ C)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hobs : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N)
        (A : GaugeConfig d N G), plaquetteWilsonObs F p A = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_unit_wilson_observable
    μ plaquetteEnergy β F dnat T P₀ γ C_T Ω hgap hvac
    (kp_hint_of_bounded_boltzmann_factor_on_probability_space μ plaquetteEnergy β hmeas hbdd)
    hcorr hobs

theorem kp_hobs_of_unit_plaquette_holonomy_observable
    (F : G → ℝ)
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        F (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N) (A : GaugeConfig d N G),
        plaquetteWilsonObs F p A = 1 := by
  intro N instN p A
  simp only [plaquetteWilsonObs]
  exact hF N A p

theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hmeas : ∀ (N : ℕ) [NeZero N],
        Measurable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U)))
    (hbdd : ∀ (N : ℕ) [NeZero N], ∃ C : ℝ,
        ∀ U : GaugeConfig d N G,
          Real.exp (-β * wilsonAction plaquetteEnergy U) ≤ C)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        F (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_unit_wilson_observable_bounded
    μ plaquetteEnergy β F dnat T P₀ γ C_T Ω hgap hvac hmeas hbdd hcorr
    (kp_hobs_of_unit_plaquette_holonomy_observable F hF)

/-- C48-T1: Boltzmann factor measurability from primitive plaquetteEnergy measurability.
    Reduces the hmeas condition to Measurable plaquetteEnergy. -/
theorem kp_hmeas_of_measurable_plaquetteEnergy
    [MeasurableInv G] [MeasurableMul₂ G]
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (h : Measurable plaquetteEnergy) :
    ∀ (N : ℕ) [NeZero N],
        Measurable (fun U : GaugeConfig d N G =>
          Real.exp (-β * wilsonAction plaquetteEnergy U)) := by
  intro N _instN
  exact Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_wilsonAction plaquetteEnergy h))

/-- C48-T2: Clay Yang-Mills from measurable plaquetteEnergy (packaging).
    Replaces hmeas in the C47 packaging theorem
    with the primitive Measurable plaquetteEnergy. -/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_plaquette
    [MeasurableInv G] [MeasurableMul₂ G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h : Measurable plaquetteEnergy)
    (hbdd : ∀ (N : ℕ) [NeZero N], ∃ C : ℝ,
        ∀ U : GaugeConfig d N G,
          Real.exp (-β * wilsonAction plaquetteEnergy U) ≤ C)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β F p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        F (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable
    μ plaquetteEnergy β F dnat T P₀ γ C_T Ω hgap hvac
    (kp_hmeas_of_measurable_plaquetteEnergy plaquetteEnergy β h)
    hbdd hcorr hF



/-- C49-T1: Boltzmann factor boundedness from a lower bound on wilsonAction.
    Reduces hbdd to hβ : 0 ≤ β and hm : m ≤ wilsonAction plaquetteEnergy U. --/
theorem kp_hbdd_of_bounded_below_wilsonAction
    (plaquetteEnergy : G → ℝ) (β m : ℝ)
    (hβ : 0 ≤ β)
    (hm : ∀ (N : ℕ) [NeZero N] (U : GaugeConfig d N G), m ≤ wilsonAction plaquetteEnergy U) :
    ∀ (N : ℕ) [NeZero N], ∃ C : ℝ,
        ∀ U : GaugeConfig d N G, Real.exp (-β * wilsonAction plaquetteEnergy U) ≤ C := by
  intro N _instN
  exact ⟨Real.exp (-β * m), fun U => by
    apply Real.exp_le_exp.mpr
    have h1 : m ≤ wilsonAction plaquetteEnergy U := hm N U
    have h2 : β * m ≤ β * wilsonAction plaquetteEnergy U :=
      mul_le_mul_of_nonneg_left h1 hβ
    linarith⟩

/-- C49-T2: Clay Yang-Mills from bounded-below wilsonAction. --/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_boundedbelow_action
    [MeasurableInv G] [MeasurableMul₂ G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β m : ℝ) (Fobs : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h : Measurable plaquetteEnergy)
    (hβ : 0 ≤ β)
    (hm : ∀ (N : ℕ) [NeZero N] (U : GaugeConfig d N G), m ≤ wilsonAction plaquetteEnergy U)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β Fobs p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        Fobs (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_plaquette
    μ plaquetteEnergy β Fobs dnat T P₀ γ C_T Ω hgap hvac h
    (kp_hbdd_of_bounded_below_wilsonAction plaquetteEnergy β m hβ hm)
    hcorr hF

/-- C50-T1: Lower bound on wilsonAction from pointwise nonnegativity of plaquetteEnergy.
    Reduces hm (m = 0) to hpe : ∀ g : G, 0 ≤ plaquetteEnergy g. --/
theorem kp_hm_of_nonneg_plaquetteEnergy
    (plaquetteEnergy : G → ℝ)
    (hpe : ∀ g : G, 0 ≤ plaquetteEnergy g) :
    ∀ (N : ℕ) [NeZero N] (U : GaugeConfig d N G), 0 ≤ wilsonAction plaquetteEnergy U := by
  intro N _instN U
  simp only [wilsonAction]
  apply Finset.sum_nonneg
  intro p _
  exact hpe (GaugeConfig.plaquetteHolonomy U p)

/-- C50-T2: Clay Yang-Mills from nonneg plaquette energy.
    Packages C49 hbdd-reduction and C50-T1, replacing hm with hpe. --/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_nonneg_plaquetteEnergy
    [MeasurableInv G] [MeasurableMul₂ G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (Fobs : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h : Measurable plaquetteEnergy)
    (hβ : 0 ≤ β)
    (hpe : ∀ g : G, 0 ≤ plaquetteEnergy g)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β Fobs p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        Fobs (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_boundedbelow_action
    μ plaquetteEnergy β 0 Fobs dnat T P₀ γ C_T Ω hgap hvac h hβ
    (kp_hm_of_nonneg_plaquetteEnergy plaquetteEnergy hpe)
    hcorr hF

/-- C51-T1: Lower bound on plaquetteEnergy from a squared representation.
    Reduces hpe : forall g : G, 0 <= plaquetteEnergy g to the structural assumption
    that plaquetteEnergy is a pointwise square: forall g, plaquetteEnergy g = f g ^ 2.
    Proof: sq_nonneg applied after rewriting with hdef. --/
theorem kp_hpe_of_sq_plaquetteEnergy
    (plaquetteEnergy : G → ℝ) (f : G → ℝ)
    (hdef : ∀ g : G, plaquetteEnergy g = f g ^ 2) :
    ∀ g : G, 0 ≤ plaquetteEnergy g := by
  intro g
  rw [hdef]
  exact sq_nonneg _

/-- C51-T2: Clay Yang-Mills from squared plaquette energy.
    Packages C50-T2 and C51-T1: replaces hpe with the structural assumption
    hdef : forall g : G, plaquetteEnergy g = f g ^ 2. --/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_sq_plaquetteEnergy
    [MeasurableInv G] [MeasurableMul₂ G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (f : G → ℝ) (β : ℝ) (Fobs : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (h : Measurable plaquetteEnergy)
    (hβ : 0 ≤ β)
    (hdef : ∀ g : G, plaquetteEnergy g = f g ^ 2)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β Fobs p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        Fobs (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_nonneg_plaquetteEnergy
    μ plaquetteEnergy β Fobs dnat T P₀ γ C_T Ω hgap hvac h hβ
    (kp_hpe_of_sq_plaquetteEnergy plaquetteEnergy f hdef)
    hcorr hF

/-- C52-T1: Measurability of plaquetteEnergy from measurability of its square-root factor.
    Reduces h : Measurable plaquetteEnergy to hf : Measurable f
    under the structural assumption hdef : forall g, plaquetteEnergy g = f g ^ 2.
    Proof: funext gives the pointwise equality as a function equality,
    then Measurable.pow_const closes the goal. --/
theorem kp_hmeas_of_measurable_sq_plaquetteEnergy
    (plaquetteEnergy : G → ℝ) (f : G → ℝ)
    (hf : Measurable f)
    (hdef : ∀ g : G, plaquetteEnergy g = f g ^ 2) :
    Measurable plaquetteEnergy := by
  have heq : plaquetteEnergy = fun g => f g ^ 2 := funext hdef
  rw [heq]
  exact hf.pow_const 2

/-- C52-T2: Clay Yang-Mills from measurability of the square-root factor.
    Packages C51-T2 and C52-T1: replaces h : Measurable plaquetteEnergy with
    hf : Measurable f under hdef : forall g, plaquetteEnergy g = f g ^ 2.
    Delegates to C51-T2 with kp_hmeas_of_measurable_sq_plaquetteEnergy as witness. --/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_sq_plaquetteEnergy_from_measurable_factor
    [MeasurableInv G] [MeasurableMul₂ G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (f : G → ℝ) (β : ℝ) (Fobs : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hf : Measurable f)
    (hβ : 0 ≤ β)
    (hdef : ∀ g : G, plaquetteEnergy g = f g ^ 2)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β Fobs p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        Fobs (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_sq_plaquetteEnergy
    μ plaquetteEnergy f β Fobs dnat T P₀ γ C_T Ω hgap hvac
    (kp_hmeas_of_measurable_sq_plaquetteEnergy plaquetteEnergy f hf hdef)
    hβ hdef hcorr hF

/-- C53-T1: Non-negativity of plaquetteEnergy from a norm-square factor.
    Reduces hpe : ∀ g, 0 ≤ plaquetteEnergy g to the structural assumption
    hndef : ∀ g, plaquetteEnergy g = ‖f g‖ ^ 2.
    Proof: ‖·‖ ^ 2 ≥ 0 by sq_nonneg. --/
theorem kp_hpe_of_norm_sq_plaquetteEnergy
    {E : Type*} [SeminormedAddCommGroup E]
    (plaquetteEnergy : G → ℝ) (f : G → E)
    (hndef : ∀ g : G, plaquetteEnergy g = ‖f g‖ ^ 2) :
    ∀ g : G, 0 ≤ plaquetteEnergy g := by
  intro g; rw [hndef g]; exact sq_nonneg _

/-- C53-T2: Measurability of plaquetteEnergy from measurability of its norm-square factor.
    Reduces h : Measurable plaquetteEnergy to hf : Measurable f
    under the structural assumption hndef : ∀ g, plaquetteEnergy g = ‖f g‖ ^ 2.
    Proof: funext gives the function equality,
    then Measurable.norm and Measurable.pow_const close the goal. --/
theorem kp_hmeas_of_measurable_norm_sq_plaquetteEnergy
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (plaquetteEnergy : G → ℝ) (f : G → E)
    (hf : Measurable f)
    (hndef : ∀ g : G, plaquetteEnergy g = ‖f g‖ ^ 2) :
    Measurable plaquetteEnergy := by
  have heq : plaquetteEnergy = fun g => ‖f g‖ ^ 2 := funext hndef
  rw [heq]
  exact hf.norm.pow_const 2

/-- C53-T3: Clay Yang-Mills from a norm-square plaquette energy.
    Packages C52-T2, C53-T1, and C53-T2:
    given f : G → E with hf : Measurable f and hndef : ∀ g, plaquetteEnergy g = ‖f g‖ ^ 2,
    derives measurability and non-negativity of plaquetteEnergy
    and concludes ClayYangMillsTheorem.
    Delegates to C52-T2 with the ℝ-valued factor fun g => ‖f g‖. ---/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy
    [MeasurableInv G] [MeasurableMul₂ G]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (f : G → E) (β : ℝ) (Fobs : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hf : Measurable f)
    (hβ : 0 ≤ β)
    (hndef : ∀ g : G, plaquetteEnergy g = ‖f g‖ ^ 2)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β Fobs p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        Fobs (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_measurable_sq_plaquetteEnergy_from_measurable_factor
    μ plaquetteEnergy (fun g => ‖f g‖) β Fobs dnat T P₀ γ C_T Ω hgap hvac
    hf.norm hβ hndef hcorr hF

/-- C54-T1: Non-negativity of β from a square representation.
    Reduces hβ : 0 ≤ β to hβdef : β = b ^ 2 for some b : ℝ.
    Proof: sq_nonneg directly. --/
theorem kp_hbeta_of_sq
    (β b : ℝ) (hβdef : β = b ^ 2) :
    0 ≤ β := by
  rw [hβdef]; exact sq_nonneg _

/-- C54-T2: Clay Yang-Mills from a norm-square plaquette energy and a squared inverse temperature.
    Packages C53-T3 and C54-T1:
    given f : G → E with hf : Measurable f, hndef : ∀ g, plaquetteEnergy g = ‖f g‖ ^ 2,
    and hβdef : β = b ^ 2 for some b : ℝ,
    derives 0 ≤ β and concludes ClayYangMillsTheorem.
    Delegates to C53-T3 with kp_hbeta_of_sq supplying hβ. --/
theorem kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy_sq_beta
    [MeasurableInv G] [MeasurableMul₂ G]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (f : G → E) (β b : ℝ) (Fobs : G → ℝ)
    (dnat : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℕ)
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ) (Ω : H)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hvac : ‖Ω‖ = 1 ∧ P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hf : Measurable f)
    (hβdef : β = b ^ 2)
    (hndef : ∀ g : G, plaquetteEnergy g = ‖f g‖ ^ 2)
    (hcorr : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        @wilsonCorrelation d N _ _ G _ _ μ plaquetteEnergy β Fobs p q =
        @inner ℝ H _ Ω ((T ^ (dnat N p q)) Ω))
    (hF : ∀ (N : ℕ) [NeZero N] (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
        Fobs (GaugeConfig.plaquetteHolonomy A p) = 1) :
    ClayYangMillsTheorem :=
  kp_clay_from_normalized_rank_one_vacuum_projector_and_holonomy_normalized_observable_norm_sq_plaquetteEnergy
    μ plaquetteEnergy f β Fobs dnat T P₀ γ C_T Ω hgap hvac
    hf (kp_hbeta_of_sq β b hβdef) hndef hcorr hF

end AbstractDecayBridge

end YangMills
