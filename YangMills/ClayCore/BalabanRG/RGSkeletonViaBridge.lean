import Mathlib
import YangMills.ClayCore.BalabanRG.RGBridgeCompatibility

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# RGSkeletonViaBridge — Layer 11H (v0.9.13)

Facade layer: exposes skeleton-style API implemented via bridge logic.
Higher layers import this to begin migration without touching baseline files.

## API contract

- `large_field_bound_via_bridge`: P80-style suppression
- `cauchy_bound_via_bridge`: P81-style Cauchy decay
- `rg_increment_decay_via_bridge`: combined P80+P81

These have the same logical content as the skeleton theorems
but flow through RGViaBridgeControl.
-/

noncomputable section

variable {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}

/-- P80 suppression matching skeleton signature. 0 sorrys. -/
theorem large_field_bound_via_bridge
    (ctrl : RGViaBridgeControl d N_c k β) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K).largePart
        (ctrl.bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_suppression_from_bridge ctrl K

/-- P81 Cauchy decay matching skeleton signature. 0 sorrys. -/
theorem cauchy_bound_via_bridge
    (ctrl : RGViaBridgeControl d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  cauchy_decay_from_bridge ctrl K₁ K₂ C hC

/-- Combined P80+P81 matching skeleton signature. 0 sorrys. -/
theorem rg_increment_decay_via_bridge
    (ctrl : RGViaBridgeControl d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    (ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
      C * ActivityNorm.dist K₁ K₂) :=
  rg_increment_decay_from_bridge ctrl K₁ K₂ C hC

/-- Convenience: P80 for any bridge directly (no ctrl). 0 sorrys. -/
theorem large_field_bound_any_bridge
    (bridge : ActivityFieldBridge d k) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).largePart
        (bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_suppression_any_bridge bridge K

/-- Convenience: P81 for any bridge directly (no ctrl). 0 sorrys. -/
theorem cauchy_bound_any_bridge
    (bridge : ActivityFieldBridge d k)
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  cauchy_decay_any_bridge bridge K₁ K₂ C hC

end

end YangMills.ClayCore
