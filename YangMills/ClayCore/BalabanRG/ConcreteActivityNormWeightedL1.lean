import Mathlib
import YangMills.ClayCore.BalabanRG.ConcreteActivityNormL1

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ConcreteActivityNormWeightedL1 — (v1.0.12-alpha Phase 1)

A first weighted extension of the concrete finite `L¹` activity norm.

We introduce a nonnegative weight
  w : Polymer ... → ℝ
and define

  ‖K‖_{w,1} = ∑ p, |K p| * w p.

This is still conservative:
- no KP-style exponential weight yet,
- no polymer size machinery required,
- but it is the first bridge from plain `L¹` to a weighted norm architecture.

The key discharge is:
if `1 ≤ w p` for all `p`, then evaluation is still bounded by
`dist(K,0)` in the weighted norm.
-/

noncomputable section

section WeightedL1

variable {d k : ℕ}
variable [Fintype (Polymer d (Int.ofNat k))]
variable [DecidableEq (Polymer d (Int.ofNat k))]

/-- Weighted finite `L¹` norm on activity families. -/
def activityWeightedL1Norm
    (w : Polymer d (Int.ofNat k) → ℝ)
    (K : ActivityFamily d k) : ℝ :=
  ∑ p, |K p| * w p

theorem activityWeightedL1Norm_nonneg
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (K : ActivityFamily d k) :
    0 ≤ activityWeightedL1Norm (d := d) (k := k) w K := by
  unfold activityWeightedL1Norm
  exact Finset.sum_nonneg (by
    intro p hp
    exact mul_nonneg (abs_nonneg (K p)) (hw_nonneg p))

theorem activityWeightedL1Norm_zero
    (w : Polymer d (Int.ofNat k) → ℝ) :
    activityWeightedL1Norm (d := d) (k := k) w
      (fun _ : Polymer d (Int.ofNat k) => (0 : ℝ)) = 0 := by
  simp [activityWeightedL1Norm]

theorem activityWeightedL1Norm_add_le
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (K₁ K₂ : ActivityFamily d k) :
    activityWeightedL1Norm (d := d) (k := k) w (fun p => K₁ p + K₂ p) ≤
      activityWeightedL1Norm (d := d) (k := k) w K₁ +
      activityWeightedL1Norm (d := d) (k := k) w K₂ := by
  unfold activityWeightedL1Norm
  calc
    ∑ p, |K₁ p + K₂ p| * w p
      ≤ ∑ p, ((|K₁ p| + |K₂ p|) * w p) := by
          exact Finset.sum_le_sum (by
            intro p hp
            have habs : |K₁ p + K₂ p| ≤ |K₁ p| + |K₂ p| := abs_add_le _ _
            exact mul_le_mul_of_nonneg_right habs (hw_nonneg p))
    _ = ∑ p, (|K₁ p| * w p + |K₂ p| * w p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = (∑ p, |K₁ p| * w p) + (∑ p, |K₂ p| * w p) := by
          rw [Finset.sum_add_distrib]

theorem activityWeightedL1Norm_neg
    (w : Polymer d (Int.ofNat k) → ℝ)
    (K : ActivityFamily d k) :
    activityWeightedL1Norm (d := d) (k := k) w (fun p => -K p) =
      activityWeightedL1Norm (d := d) (k := k) w K := by
  unfold activityWeightedL1Norm
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp

theorem activityWeightedL1Norm_smul
    (w : Polymer d (Int.ofNat k) → ℝ)
    (c : ℝ) (K : ActivityFamily d k) :
    activityWeightedL1Norm (d := d) (k := k) w (fun p => c * K p) =
      |c| * activityWeightedL1Norm (d := d) (k := k) w K := by
  unfold activityWeightedL1Norm
  calc
    ∑ p, |c * K p| * w p = ∑ p, (|c| * |K p|) * w p := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [abs_mul]
    _ = ∑ p, |c| * (|K p| * w p) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = |c| * ∑ p, (|K p| * w p) := by
      rw [← Finset.mul_sum]
    _ = |c| * activityWeightedL1Norm (d := d) (k := k) w K := by
      rfl

theorem activityWeightedL1Norm_eq_zero
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_ge_one : ∀ p, 1 ≤ w p)
    (K : ActivityFamily d k)
    (hK : activityWeightedL1Norm (d := d) (k := k) w K = 0) :
    ∀ p, K p = 0 := by
  intro p
  have hsum :
      ∀ q ∈ (Finset.univ : Finset (Polymer d (Int.ofNat k))), |K q| * w q = 0 := by
    have hw_nonneg : ∀ q, 0 ≤ w q := by
      intro q
      linarith [hw_ge_one q]
    apply (Finset.sum_eq_zero_iff_of_nonneg (by
      intro q hq
      exact mul_nonneg (abs_nonneg (K q)) (hw_nonneg q))).mp
    simpa [activityWeightedL1Norm] using hK
  have hp0 : |K p| * w p = 0 := hsum p (by simp)
  have hwp : 0 < w p := by
    linarith [hw_ge_one p]
  have habs : |K p| = 0 := by
    exact (mul_eq_zero.mp hp0).resolve_right (ne_of_gt hwp)
  exact abs_eq_zero.mp habs

/-- Weighted finite `L¹` instance of `ActivityNorm`. -/
instance instActivityNormWeightedL1
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_ge_one : ∀ p, 1 ≤ w p) :
    ActivityNorm d k where
  norm := activityWeightedL1Norm (d := d) (k := k) w
  norm_nonneg := activityWeightedL1Norm_nonneg (d := d) (k := k) w hw_nonneg
  norm_zero := activityWeightedL1Norm_zero (d := d) (k := k) w
  norm_add_le := activityWeightedL1Norm_add_le (d := d) (k := k) w hw_nonneg
  norm_neg := activityWeightedL1Norm_neg (d := d) (k := k) w
  norm_smul := activityWeightedL1Norm_smul (d := d) (k := k) w
  norm_eq_zero := activityWeightedL1Norm_eq_zero (d := d) (k := k) w hw_ge_one

end WeightedL1

section WeightedFamily

variable {d : ℕ}
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Family version of the weighted finite `L¹` norm. -/
instance instActivityNormWeightedL1All
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p) :
    ∀ j, ActivityNorm d j :=
  fun j => instActivityNormWeightedL1 (d := d) (k := j) (w j) (hw_nonneg j) (hw_ge_one j)

end WeightedFamily

section Evaluation

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Evaluation is bounded by the weighted norm provided `1 ≤ w p`. 0 sorrys. -/
theorem activityNormEvaluationBoundAt_weightedL1
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    ActivityNormEvaluationBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  intro K
  have hpoint : |K p₀| ≤ |K p₀| * w k p₀ := by
    have hw1 : 1 ≤ w k p₀ := hw_ge_one k p₀
    have hnonneg : 0 ≤ |K p₀| := abs_nonneg (K p₀)
    have hmul := mul_le_mul_of_nonneg_left hw1 hnonneg
    simpa [one_mul] using hmul
  have hsingle :
      |K p₀| * w k p₀ ≤ ∑ p, |K p| * w k p := by
    simpa using
      (Finset.single_le_sum
        (fun q _ => mul_nonneg (abs_nonneg (K q)) (hw_nonneg k q))
        (by simp : p₀ ∈ (Finset.univ : Finset (Polymer d (Int.ofNat k)))))
  calc
    |K p₀| ≤ |K p₀| * w k p₀ := hpoint
    _ ≤ ∑ p, |K p| * w k p := hsingle
    _ = activityWeightedL1Norm (d := d) (k := k) (w k) K := by
      rfl
    _ = ActivityNorm.dist K (fun _ => 0) := by
      rw [ActivityNorm.dist_zero_right]
      rfl
    _ = 1 * ActivityNorm.dist K (fun _ => 0) := by
      ring

/-- Weighted Cauchy evaluation bound follows from the weighted evaluation bound.
0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_weightedL1
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    ActivityNormEvaluationCauchyBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  exact activityNormEvaluationCauchyBoundAt_of_eval
    (d := d) (N_c := N_c) k 1 p₀
    (activityNormEvaluationBoundAt_weightedL1
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k p₀)

end Evaluation

end

end YangMills.ClayCore
