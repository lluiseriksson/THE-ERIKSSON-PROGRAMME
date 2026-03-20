import Mathlib
import YangMills.ClayCore.BalabanRG.ActivityNormDifferenceCompatibility

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ConcreteActivityNormL1 — (v1.0.10-alpha Phase 1, conservative)

First concrete `ActivityNorm` instance for finite polymer types.

We use the finite `L¹` norm
  ‖K‖₁ = ∑ p, |K p|.

This file is deliberately conservative:
- define the finite `L¹` norm at one scale `k`,
- package it as an `ActivityNorm d k`,
- lift it to a family `∀ j, ActivityNorm d j`,
- discharge the native evaluation bound with constant `1`,
- derive the native Cauchy evaluation bound from it.

We do not yet force a high-level bridge consumer in this file.
-/

noncomputable section

section L1Norm

variable {d k : ℕ}
variable [Fintype (Polymer d (Int.ofNat k))]
variable [DecidableEq (Polymer d (Int.ofNat k))]

/-- Finite `L¹` norm on activity families. -/
def activityL1Norm (K : ActivityFamily d k) : ℝ :=
  ∑ p, |K p|

theorem activityL1Norm_nonneg (K : ActivityFamily d k) : 0 ≤ activityL1Norm (d := d) (k := k) K := by
  unfold activityL1Norm
  exact Finset.sum_nonneg (by
    intro p hp
    exact abs_nonneg (K p))

theorem activityL1Norm_zero :
    activityL1Norm (d := d) (k := k) (fun _ : Polymer d (Int.ofNat k) => (0 : ℝ)) = 0 := by
  simp [activityL1Norm]

theorem activityL1Norm_add_le (K₁ K₂ : ActivityFamily d k) :
    activityL1Norm (d := d) (k := k) (fun p => K₁ p + K₂ p) ≤
      activityL1Norm (d := d) (k := k) K₁ + activityL1Norm (d := d) (k := k) K₂ := by
  unfold activityL1Norm
  calc
    ∑ p, |K₁ p + K₂ p|
      ≤ ∑ p, (|K₁ p| + |K₂ p|) := by
          exact Finset.sum_le_sum (by
            intro p hp
            simpa using abs_add_le (K₁ p) (K₂ p))
    _ = (∑ p, |K₁ p|) + (∑ p, |K₂ p|) := by
          rw [Finset.sum_add_distrib]

theorem activityL1Norm_neg (K : ActivityFamily d k) :
    activityL1Norm (d := d) (k := k) (fun p => -K p) =
      activityL1Norm (d := d) (k := k) K := by
  unfold activityL1Norm
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp

theorem activityL1Norm_smul (c : ℝ) (K : ActivityFamily d k) :
    activityL1Norm (d := d) (k := k) (fun p => c * K p) =
      |c| * activityL1Norm (d := d) (k := k) K := by
  unfold activityL1Norm
  calc
    ∑ p, |c * K p| = ∑ p, |c| * |K p| := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [abs_mul]
    _ = |c| * ∑ p, |K p| := by
      rw [← Finset.mul_sum]
    _ = |c| * activityL1Norm (d := d) (k := k) K := by
      rfl

theorem activityL1Norm_eq_zero (K : ActivityFamily d k)
    (hK : activityL1Norm (d := d) (k := k) K = 0) :
    ∀ p, K p = 0 := by
  intro p
  have hsum :
      ∀ q ∈ (Finset.univ : Finset (Polymer d (Int.ofNat k))), |K q| = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (by
      intro q hq
      exact abs_nonneg (K q))).mp
    simpa [activityL1Norm] using hK
  have hp : |K p| = 0 := hsum p (by simp)
  exact abs_eq_zero.mp hp

/-- Concrete finite `L¹` instance of `ActivityNorm`. -/
instance instActivityNormL1 : ActivityNorm d k where
  norm := activityL1Norm (d := d) (k := k)
  norm_nonneg := activityL1Norm_nonneg (d := d) (k := k)
  norm_zero := activityL1Norm_zero (d := d) (k := k)
  norm_add_le := activityL1Norm_add_le (d := d) (k := k)
  norm_neg := activityL1Norm_neg (d := d) (k := k)
  norm_smul := activityL1Norm_smul (d := d) (k := k)
  norm_eq_zero := activityL1Norm_eq_zero (d := d) (k := k)

end L1Norm

section L1Family

variable {d : ℕ}
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Family version: the finite `L¹` norm gives an `ActivityNorm` at every scale. -/
instance instActivityNormL1All : ∀ j, ActivityNorm d j :=
  fun j => instActivityNormL1 (d := d) (k := j)

end L1Family

section Evaluation

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- For the concrete `L¹` norm family, evaluation at a polymer is controlled by
`dist(K,0)` with sharp constant `1`. 0 sorrys. -/
theorem activityNormEvaluationBoundAt_l1
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    ActivityNormEvaluationBoundAt d N_c k 1 p₀ := by
  intro K
  have hsingle : |K p₀| ≤ ∑ p, |K p| := by
    simpa using
      (Finset.single_le_sum
        (fun q _ => abs_nonneg (K q))
        (by simp : p₀ ∈ (Finset.univ : Finset (Polymer d (Int.ofNat k)))))
  calc
    |K p₀| ≤ ∑ p, |K p| := hsingle
    _ = activityL1Norm (d := d) (k := k) K := by
      rfl
    _ = ActivityNorm.dist K (fun _ => 0) := by
      rw [ActivityNorm.dist_zero_right]
      rfl
    _ = 1 * ActivityNorm.dist K (fun _ => 0) := by
      ring

/-- For the concrete `L¹` norm family, the native Cauchy evaluation bound also
holds with constant `1`. 0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_l1
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    ActivityNormEvaluationCauchyBoundAt d N_c k 1 p₀ :=
  activityNormEvaluationCauchyBoundAt_of_eval
    (d := d) (N_c := N_c) k 1 p₀
    (activityNormEvaluationBoundAt_l1 (d := d) (N_c := N_c) k p₀)

/-- The singleton pointwise large-field bridge follows automatically from the
concrete `L¹` norm family. 0 sorrys. -/
theorem singletonPointwiseBound_l1
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    SingletonPointwiseBound d N_c k 1 p₀ :=
  singletonPointwiseBound_of_activityNormEvaluationBoundAt
    (d := d) (N_c := N_c) k 1 p₀
    (activityNormEvaluationBoundAt_l1 (d := d) (N_c := N_c) k p₀)

/-- The singleton pointwise Cauchy bridge follows automatically from the
concrete `L¹` norm family. 0 sorrys. -/
theorem singletonPointwiseCauchyBound_l1
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    SingletonPointwiseCauchyBound d N_c k 1 p₀ :=
  singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
    (d := d) (N_c := N_c) k 1 p₀
    (activityNormEvaluationCauchyBoundAt_l1 (d := d) (N_c := N_c) k p₀)

end Evaluation

end

end YangMills.ClayCore
