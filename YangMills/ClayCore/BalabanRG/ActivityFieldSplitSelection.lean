import Mathlib
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit
import YangMills.ClayCore.BalabanRG.ActivityFieldBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# ActivityFieldSplitSelection — Layer 15E (v0.9.7)

Dynamic selector: branches between trivial (small) and large-only split.
First non-trivial logical branching in the RG chain.
-/

noncomputable section

/-- Dynamic selector: trivial split if small, large-only split if large. -/
def selectFieldSplitViaBridge (d N_c : ℕ) [NeZero N_c] (k : ℕ)
    (bridge : ActivityFieldBridge d k) (β : ℝ)
    (K : ActivityFamily d k) :
    RGFieldSplitOnField d N_c k :=
  if SmallFieldPredViaBridge bridge N_c β K then
    trivialRGFieldSplitOnField d N_c k
  else
    largeOnlyRGFieldSplitOnField d N_c k

/-- Small field → trivial split. 0 sorrys. -/
theorem selectFieldSplitViaBridge_of_small {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hS : SmallFieldPredViaBridge bridge N_c β K) :
    selectFieldSplitViaBridge d N_c k bridge β K =
      trivialRGFieldSplitOnField d N_c k := by
  simp [selectFieldSplitViaBridge, hS]

/-- Large field → large-only split. 0 sorrys. -/
theorem selectFieldSplitViaBridge_of_large {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hL : LargeFieldPredViaBridge bridge N_c β K) :
    selectFieldSplitViaBridge d N_c k bridge β K =
      largeOnlyRGFieldSplitOnField d N_c k := by
  have hnotS := not_small_of_large_via_bridge bridge N_c β K hL
  simp [selectFieldSplitViaBridge, hnotS]

/-- Small case: large part is zero. 0 sorrys. -/
theorem selectViaBridge_largePart_zero_of_small {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hS : SmallFieldPredViaBridge bridge N_c β K)
    (φ : BalabanLatticeSite d k → ℝ) :
    (selectFieldSplitViaBridge d N_c k bridge β K).largePart φ K = fun _ => 0 := by
  rw [selectFieldSplitViaBridge_of_small bridge β K hS]; rfl

/-- Large case: small part is zero. 0 sorrys. -/
theorem selectViaBridge_smallPart_zero_of_large {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hL : LargeFieldPredViaBridge bridge N_c β K)
    (φ : BalabanLatticeSite d k → ℝ) :
    (selectFieldSplitViaBridge d N_c k bridge β K).smallPart φ K = fun _ => 0 := by
  rw [selectFieldSplitViaBridge_of_large bridge β K hL]; rfl

/-- Large case: large part equals RG map. 0 sorrys. -/
theorem selectViaBridge_largePart_eq_rg_of_large {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (hL : LargeFieldPredViaBridge bridge N_c β K)
    (φ : BalabanLatticeSite d k → ℝ) :
    (selectFieldSplitViaBridge d N_c k bridge β K).largePart φ K =
      RGBlockingMap d N_c k K := by
  rw [selectFieldSplitViaBridge_of_large bridge β K hL]; rfl

/-- Zero activity always uses trivial split. 0 sorrys. -/
theorem zero_activity_uses_trivial {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) :
    selectFieldSplitViaBridge d N_c k bridge β (fun _ => 0) =
      trivialRGFieldSplitOnField d N_c k :=
  selectFieldSplitViaBridge_of_small bridge β _ (zero_activity_small bridge N_c β)

end

end YangMills.ClayCore
