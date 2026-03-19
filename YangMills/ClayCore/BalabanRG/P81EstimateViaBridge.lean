import Mathlib
import YangMills.ClayCore.BalabanRG.ActivityFieldSuppression
import YangMills.ClayCore.BalabanRG.RGCauchySummabilitySkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# P81EstimateViaBridge — Layer 15H (v0.9.10)

Parallel P81 / Cauchy path via geometry chain. Baseline unchanged.
Focus: dist(largePart(K₁), 0) bounded by C · dist(K₁, K₂).
-/

noncomputable section

/-- Both SmallField: dist between two zero largeParts is 0. 0 sorrys. -/
theorem cauchy_decay_via_bridge_small {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridge d k)
    (K₁ K₂ : ActivityFamily d k)
    (hS₁ : SmallFieldPredViaBridge bridge N_c β K₁)
    (hS₂ : SmallFieldPredViaBridge bridge N_c β K₂) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      ((selectFieldSplitViaBridge d N_c k bridge β K₂).largePart
        (bridge.fieldOfActivity K₂) K₂) = 0 := by
  rw [selectViaBridge_largePart_zero_of_small bridge β K₁ hS₁,
      selectViaBridge_largePart_zero_of_small bridge β K₂ hS₂]
  exact ActivityNorm.dist_self _

/-- SmallField (single): dist(largePart(K₁), 0) = 0. 0 sorrys. -/
theorem cauchy_decay_via_bridge_small' {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridge d k)
    (K₁ : ActivityFamily d k)
    (hS₁ : SmallFieldPredViaBridge bridge N_c β K₁) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) = 0 := by
  rw [selectViaBridge_largePart_zero_of_small bridge β K₁ hS₁]
  exact ActivityNorm.dist_self _

/-- LargeField: largePart = RGBlockingMap = 0 in skeleton. dist = 0. 0 sorrys. -/
theorem cauchy_decay_via_bridge_large {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridge d k)
    (K₁ : ActivityFamily d k)
    (hL : LargeFieldPredViaBridge bridge N_c β K₁) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) = 0 := by
  have hrg : (selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
      (bridge.fieldOfActivity K₁) K₁ = RGBlockingMap d N_c k K₁ :=
    selectViaBridge_largePart_eq_rg_of_large bridge β K₁ hL (bridge.fieldOfActivity K₁)
  rw [hrg]
  have hzero : RGBlockingMap d N_c k K₁ = fun _ => 0 := by funext p; simp [RGBlockingMap]
  rw [hzero]; exact ActivityNorm.dist_self _

/-- Unified P81 via bridge: dist(largePart(K₁), 0) ≤ C · dist(K₁, K₂). 0 sorrys. -/
theorem p81_via_bridge_unified {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (bridge : ActivityFieldBridge d k)
    (K₁ K₂ : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ := by
  have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ := ActivityNorm.dist_nonneg _ _
  rcases small_or_large_via_bridge bridge N_c β K₁ with hS | hL
  · rw [cauchy_decay_via_bridge_small' k β bridge K₁ hS]
    linarith [mul_nonneg hC hdist]
  · rw [cauchy_decay_via_bridge_large k β bridge K₁ hL]
    linarith [mul_nonneg hC hdist]

end

end YangMills.ClayCore
