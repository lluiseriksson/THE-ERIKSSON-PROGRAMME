import Mathlib
import YangMills.ClayCore.BalabanRG.ActivityFieldSplitSelection

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# ActivityFieldSuppression — Layer 15F (v0.9.8)

High-level API for large-field suppression via the dynamic selector.
Converts selector branching into consumption-ready theorems.

## Key results

- `largeField_part_vanishes_on_small`: largePart = 0 when K is small
- `smallField_part_vanishes_on_large`: smallPart = 0 when K is large
- `selected_split_cases`: binary case analysis
- `suppression_bound_small`: dist(largePart(K), 0) = 0 when small

These are the structural predecessors of the P80 estimate.
-/

noncomputable section

/-- Binary case analysis for the selected split. 0 sorrys. -/
theorem selected_split_cases {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k) :
    selectFieldSplitViaBridge d N_c k bridge β K = trivialRGFieldSplitOnField d N_c k ∨
    selectFieldSplitViaBridge d N_c k bridge β K = largeOnlyRGFieldSplitOnField d N_c k := by
  unfold selectFieldSplitViaBridge
  by_cases h : SmallFieldPredViaBridge bridge N_c β K
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h])

/-- Large part vanishes when activity induces a small field. 0 sorrys. -/
theorem largeField_part_vanishes_on_small {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hS : SmallFieldPredViaBridge bridge N_c β K)
    (φ : BalabanLatticeSite d k → ℝ) :
    (selectFieldSplitViaBridge d N_c k bridge β K).largePart φ K = fun _ => 0 :=
  selectViaBridge_largePart_zero_of_small bridge β K hS φ

/-- Small part vanishes when activity induces a large field. 0 sorrys. -/
theorem smallField_part_vanishes_on_large {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hL : LargeFieldPredViaBridge bridge N_c β K)
    (φ : BalabanLatticeSite d k → ℝ) :
    (selectFieldSplitViaBridge d N_c k bridge β K).smallPart φ K = fun _ => 0 :=
  selectViaBridge_smallPart_zero_of_large bridge β K hL φ

/-- Small field: dist(largePart, 0) = 0. 0 sorrys. -/
theorem suppression_bound_small {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    [∀ j, ActivityNorm d j]
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hS : SmallFieldPredViaBridge bridge N_c β K)
    (φ : BalabanLatticeSite d k → ℝ) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).largePart φ K)
      (fun _ => 0) = 0 := by
  rw [largeField_part_vanishes_on_small bridge β K hS φ]
  exact ActivityNorm.dist_self _

/-- Large field: dist(smallPart, 0) = 0. 0 sorrys. -/
theorem suppression_bound_large {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    [∀ j, ActivityNorm d j]
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hL : LargeFieldPredViaBridge bridge N_c β K)
    (φ : BalabanLatticeSite d k → ℝ) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).smallPart φ K)
      (fun _ => 0) = 0 := by
  rw [smallField_part_vanishes_on_large bridge β K hL φ]
  exact ActivityNorm.dist_self _

end

end YangMills.ClayCore
