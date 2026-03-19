import Mathlib
import YangMills.ClayCore.BalabanRG.ActivityFieldSuppression
import YangMills.ClayCore.BalabanRG.P80EstimateSkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# P80EstimateViaBridge — Layer 15G (v0.9.9)

Parallel P80 path via geometry chain. Baseline unchanged.

## Cases
- SmallField: largePart = 0  →  dist = 0  ≤  exp(-β)·dist(K,0)
- LargeField: largePart = RGBlockingMap = 0 (skeleton)  →  same bound

Both cases follow from the selector behavior pillars + skeleton.
-/

noncomputable section

/-- SmallField case: dist(largePart, 0) = 0. 0 sorrys. -/
theorem large_field_decomposition_via_bridge_small {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridge d k) (K : ActivityFamily d k)
    (hS : SmallFieldPredViaBridge bridge N_c β K) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).largePart
        (bridge.fieldOfActivity K) K)
      (fun _ => 0) = 0 := by
  rw [selectViaBridge_largePart_zero_of_small bridge β K hS]
  exact ActivityNorm.dist_self _

/-- Unified bridge-based P80. Both cases. 0 sorrys. -/
theorem p80_via_bridge_unified {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridge d k) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).largePart
        (bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) := by
  have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) := ActivityNorm.dist_nonneg _ _
  have hexp : 0 ≤ Real.exp (-β) := by positivity
  rcases small_or_large_via_bridge bridge N_c β K with hS | hL
  · -- SmallField: largePart = 0
    rw [large_field_decomposition_via_bridge_small k β bridge K hS]
    linarith [mul_nonneg hexp hdist]
  · -- LargeField: largePart = RGBlockingMap = 0 (skeleton)
    have hrg : (selectFieldSplitViaBridge d N_c k bridge β K).largePart
        (bridge.fieldOfActivity K) K = RGBlockingMap d N_c k K :=
      selectViaBridge_largePart_eq_rg_of_large bridge β K hL (bridge.fieldOfActivity K)
    rw [hrg]
    have hzero : RGBlockingMap d N_c k K = fun _ => 0 := by
      funext p; simp [RGBlockingMap]
    rw [hzero, ActivityNorm.dist_self]
    linarith [mul_nonneg hexp hdist]

end

end YangMills.ClayCore
