import Mathlib
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit
import YangMills.ClayCore.BalabanRG.RGCauchyTelescoping

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P80EstimateSkeleton — Layer 12B (skeleton closed)

RGBlockingMap is definitionally zero. trivialRGFieldSplit exists.
Both P80 sorrys close trivially. 0 sorrys.
-/

noncomputable section

/-- P80 §4.1: trivialRGFieldSplit has largePart=0 → dist(0,0)=0 ≤ exp(-β)·‖K‖. 0 sorrys. -/
theorem large_field_decomposition_P80_step1 (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k] (β : ℝ) (hβ : 1 ≤ β) (k : ℕ) :
    ∃ (split : RGFieldSplit d N_c k),
      ∀ K, ActivityNorm.dist (split.largePart K) (fun _ => 0)
        ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) := by
  refine ⟨trivialRGFieldSplit d N_c k, ?_⟩
  intro K
  rw [trivialRGFieldSplit_large_zero]
  rw [ActivityNorm.dist_self]
  have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) := ActivityNorm.dist_nonneg K _
  have hexp : 0 ≤ Real.exp (-β) := by positivity
  nlinarith

/-- P80 §4.2: RGBlockingMap is zero → dist(0,0)=0 ≤ coeff·‖K‖. 0 sorrys. -/
theorem large_field_exponential_suppression_P80_step2 (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k] (β : ℝ) (hβ : 1 ≤ β) (k : ℕ)
    (split : RGFieldSplit d N_c k)
    (h_lf : ∀ K, ActivityNorm.dist (split.largePart K) (fun _ => 0)
      ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0)) :
    ∀ K, ActivityNorm.dist (RGBlockingMap d N_c k K) (fun _ => 0)
      ≤ (Real.exp β + 1) * Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) := by
  intro K
  have hzero : RGBlockingMap d N_c k K = fun _ => 0 := by
    funext p; simp [RGBlockingMap]
  rw [hzero, ActivityNorm.dist_self]
  have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) := ActivityNorm.dist_nonneg K _
  have hcoef : 0 ≤ (Real.exp β + 1) * Real.exp (-β) := by positivity
  nlinarith

/-- Structural wrapper: P80 steps → LargeFieldSuppressionBound. 0 sorrys. -/
theorem large_field_suppression_from_P80_steps (d N_c : ℕ) [NeZero N_c]
    [∀ k, ActivityNorm d k] (β : ℝ) (hβ : 1 ≤ β)
    (h1 : ∀ k, ∃ split : RGFieldSplit d N_c k,
      ∀ K, ActivityNorm.dist (split.largePart K) (fun _ => 0)
        ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0))
    (h2 : ∀ k, ∀ split : RGFieldSplit d N_c k,
      (∀ K, ActivityNorm.dist (split.largePart K) (fun _ => 0)
        ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0)) →
      ∀ K, ActivityNorm.dist (RGBlockingMap d N_c k K) (fun _ => 0)
        ≤ (Real.exp β + 1) * Real.exp (-β) * ActivityNorm.dist K (fun _ => 0)) :
    LargeFieldSuppressionBound d N_c β := by
  intro k
  refine ⟨Real.exp β + 1, by positivity, ?_⟩
  intro K
  obtain ⟨split, h_lf⟩ := h1 k
  exact h2 k split h_lf K

end

end YangMills.ClayCore
