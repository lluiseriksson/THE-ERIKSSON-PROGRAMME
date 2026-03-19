import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerCombinatorics

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ActivitySpaceNorms — Layer 11A

Strong ActivityNorm interface needed for P81/P82 contraction estimates.
Adds: norm_add_le, norm_smul, norm_sub_le, norm_eq_zero, dist.
-/

noncomputable section

abbrev ActivityFamily (d : ℕ) (k : ℕ) := Polymer d (Int.ofNat k) → ℝ

/-- Strong norm interface for polymer activity spaces. -/
class ActivityNorm (d : ℕ) (k : ℕ) where
  norm         : ActivityFamily d k → ℝ
  norm_nonneg  : ∀ K, 0 ≤ norm K
  norm_zero    : norm (fun _ => 0) = 0
  norm_add_le  : ∀ K₁ K₂, norm (fun p => K₁ p + K₂ p) ≤ norm K₁ + norm K₂
  norm_neg     : ∀ K, norm (fun p => -K p) = norm K
  norm_smul    : ∀ (c : ℝ) K, norm (fun p => c * K p) = |c| * norm K
  norm_eq_zero : ∀ K, norm K = 0 → ∀ p, K p = 0

namespace ActivityNorm

variable {d k : ℕ} [ActivityNorm d k]

/-- Distance induced by the activity norm. -/
def dist (K₁ K₂ : ActivityFamily d k) : ℝ :=
  ActivityNorm.norm (fun p => K₁ p - K₂ p)

theorem dist_nonneg (K₁ K₂ : ActivityFamily d k) : 0 ≤ dist K₁ K₂ :=
  norm_nonneg _

theorem dist_self (K : ActivityFamily d k) : dist K K = 0 := by
  unfold dist
  have h0 : (fun p => K p - K p) = (fun _ => 0) := by funext p; ring
  rw [h0, norm_zero]

theorem dist_comm (K₁ K₂ : ActivityFamily d k) : dist K₁ K₂ = dist K₂ K₁ := by
  unfold dist
  have : (fun p => K₁ p - K₂ p) = (fun p => -(K₂ p - K₁ p)) := by funext p; ring
  rw [this, norm_neg]

theorem dist_triangle (K₁ K₂ K₃ : ActivityFamily d k) :
    dist K₁ K₃ ≤ dist K₁ K₂ + dist K₂ K₃ := by
  unfold dist
  have : (fun p => K₁ p - K₃ p) = (fun p => (K₁ p - K₂ p) + (K₂ p - K₃ p)) := by
    funext p; ring
  rw [this]; exact norm_add_le _ _

theorem norm_sub_le (K₁ K₂ : ActivityFamily d k) :
    norm (fun p => K₁ p - K₂ p) ≤ norm K₁ + norm K₂ := by
  have hsub : (fun p => K₁ p - K₂ p) = (fun p => K₁ p + (-K₂ p)) := by funext p; ring
  rw [hsub]
  calc norm (fun p => K₁ p + -K₂ p)
      ≤ norm K₁ + norm (fun p => -K₂ p) := norm_add_le K₁ (fun p => -K₂ p)
    _ = norm K₁ + norm K₂ := by rw [norm_neg]

end ActivityNorm

end

end YangMills.ClayCore
