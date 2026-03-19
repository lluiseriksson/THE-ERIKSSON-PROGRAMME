import Mathlib
import YangMills.ClayCore.BalabanRG.RGSkeletonViaBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# CauchyDecayViaBridge — Layer 10B (v0.9.14)

First high-level consumer migrated to the bridge path.
Reproduces CauchyDecayFromAF conclusions using RGSkeletonViaBridge.

## Proof of integration

The key theorem `cauchy_decay_via_bridge_control` shows that
any RGViaBridgeControl gives both the P80 suppression bound
and the P81 Cauchy decay bound — the same logical content
as the skeleton, but flowing through geometry.

`bridge_path_recovers_skeleton` closes the consistency circle:
trivialBridgeControl gives the same bounds as the baseline.
-/

noncomputable section

variable {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}

/-- Combined Cauchy decay via bridge control. Matches skeleton logical content.
    0 sorrys. -/
theorem cauchy_decay_via_bridge_control
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
  rg_increment_decay_via_bridge ctrl K₁ K₂ C hC

/-- P80 suppression via bridge control. 0 sorrys. -/
theorem large_field_suppression_bridge_consumer
    (ctrl : RGViaBridgeControl d N_c k β) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K).largePart
        (ctrl.bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_bound_via_bridge ctrl K

/-- P81 Cauchy decay via bridge control. 0 sorrys. -/
theorem cauchy_summability_bridge_consumer
    (ctrl : RGViaBridgeControl d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  cauchy_bound_via_bridge ctrl K₁ K₂ C hC

/-- Consistency: trivialBridgeControl gives the same P80 bound as baseline. 0 sorrys. -/
theorem bridge_path_recovers_skeleton
    (K₁ : ActivityFamily d k) :
    let ctrl := trivialBridgeControl (d := d) (N_c := N_c) k β
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0) := by
  dsimp
  exact (trivialBridgeControl (d := d) (N_c := N_c) k β).large_field_bound K₁

/-- Any bridge gives the Cauchy decay bound. 0 sorrys. -/
theorem cauchy_decay_any_bridge_consumer
    (bridge : ActivityFieldBridge d k)
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  cauchy_bound_any_bridge bridge K₁ K₂ C hC

end

end YangMills.ClayCore
