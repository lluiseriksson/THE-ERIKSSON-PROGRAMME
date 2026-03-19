import Mathlib
import YangMills.ClayCore.BalabanRG.SmallFieldLargeFieldSplit
import YangMills.ClayCore.BalabanRG.ActivityFieldBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# ActivityFieldSplitSelection — Layer 15E (v0.9.6)

Combines SmallFieldLargeFieldSplit and ActivityFieldBridge.
Lives ABOVE both: imports 15B+15D, is imported by neither.

This is the canonical API point where activity K and bridge determine
which RG field split to use.
-/

noncomputable section

/-- Select an RG field split from an activity via a bridge.
    Current: trivial split. API fixed for future nontrivial implementation. -/
def selectFieldSplitViaBridge (d N_c : ℕ) [NeZero N_c] (k : ℕ)
    (bridge : ActivityFieldBridge d k) (β : ℝ)
    (K : ActivityFamily d k) :
    RGFieldSplitOnField d N_c k :=
  trivialRGFieldSplitOnField d N_c k

theorem selectFieldSplitViaBridge_eq_trivial {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k) :
    selectFieldSplitViaBridge d N_c k bridge β K =
      trivialRGFieldSplitOnField d N_c k := rfl

theorem selectFieldSplitViaBridge_smallPart_eq_rg {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (φ : BalabanLatticeSite d k → ℝ) :
    (selectFieldSplitViaBridge d N_c k bridge β K).smallPart φ K =
      RGBlockingMap d N_c k K := rfl

theorem selectFieldSplitViaBridge_largePart_zero {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k)
    (φ : BalabanLatticeSite d k → ℝ) :
    (selectFieldSplitViaBridge d N_c k bridge β K).largePart φ K = fun _ => 0 := rfl

/-- Zero activity is small via any bridge. 0 sorrys. -/
theorem zero_activity_selects_small {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) :
    SmallFieldPredViaBridge bridge N_c β (fun _ => 0) :=
  zero_activity_small bridge N_c β

/-- Every activity is either small or large via bridge. 0 sorrys. -/
theorem small_or_large_activity_via_bridge {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (bridge : ActivityFieldBridge d k) (β : ℝ) (K : ActivityFamily d k) :
    SmallFieldPredViaBridge bridge N_c β K ∨
    LargeFieldPredViaBridge bridge N_c β K :=
  small_or_large_via_bridge bridge N_c β K

end

end YangMills.ClayCore
