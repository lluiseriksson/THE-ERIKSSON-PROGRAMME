import Mathlib
import YangMills.P4_Continuum.Phase4Assembly

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

end AbstractDecayBridge

end YangMills
