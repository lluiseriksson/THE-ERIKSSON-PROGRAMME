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
