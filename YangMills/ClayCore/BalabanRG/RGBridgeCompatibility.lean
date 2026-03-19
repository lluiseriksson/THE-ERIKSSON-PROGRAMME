import Mathlib
import YangMills.ClayCore.BalabanRG.RGViaBridge
import YangMills.ClayCore.BalabanRG.P80EstimateSkeleton
import YangMills.ClayCore.BalabanRG.RGCauchySummabilitySkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# RGBridgeCompatibility — Layer 11G (v0.9.12)

Compatibility layer: re-expresses skeleton-style estimates
using the unified RGViaBridgeControl API.

Allows higher-level consumers to migrate from P80/P81 placeholders
to the geometry-backed path without modifying baseline files.

Design: this file sits ABOVE RGViaBridge and ABOVE both skeletons.
It imports both but modifies neither.
-/

noncomputable section

variable {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}

/-! ## P80 compatibility -/

/-- P80-style suppression from bridge control. 0 sorrys. -/
theorem large_field_suppression_from_bridge
    (ctrl : RGViaBridgeControl d N_c k β) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K).largePart
        (ctrl.bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  ctrl.large_field_bound K

/-- P80 suppression for any bridge. 0 sorrys. -/
theorem large_field_suppression_any_bridge
    (bridge : ActivityFieldBridge d k) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).largePart
        (bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_suppression_from_bridge (rg_control_via_bridge k β bridge) K

/-! ## P81 compatibility -/

/-- P81-style Cauchy decay from bridge control. 0 sorrys. -/
theorem cauchy_decay_from_bridge
    (ctrl : RGViaBridgeControl d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  ctrl.cauchy_bound K₁ K₂ C hC

/-- P81 Cauchy decay for any bridge. 0 sorrys. -/
theorem cauchy_decay_any_bridge
    (bridge : ActivityFieldBridge d k)
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  cauchy_decay_from_bridge (rg_control_via_bridge k β bridge) K₁ K₂ C hC

/-! ## Combined compatibility -/

/-- Combined P80+P81 compatibility. Both bounds from one ctrl. 0 sorrys. -/
theorem rg_increment_decay_from_bridge
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
  ⟨ctrl.large_field_bound K₁, ctrl.cauchy_bound K₁ K₂ C hC⟩

/-- The trivial bridge satisfies both P80+P81 compatibility bounds. 0 sorrys. -/
theorem trivial_bridge_satisfies_rg_compat
    (K₁ K₂ : ActivityFamily d k) (C : ℝ) (hC : 0 ≤ C) :
    (ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k
          (trivialBridgeControl (d := d) (N_c := N_c) k β).bridge β K₁).largePart
        ((trivialBridgeControl (d := d) (N_c := N_c) k β).bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k
          (trivialBridgeControl (d := d) (N_c := N_c) k β).bridge β K₁).largePart
        ((trivialBridgeControl (d := d) (N_c := N_c) k β).bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
      C * ActivityNorm.dist K₁ K₂) :=
  rg_increment_decay_from_bridge
    (ctrl := trivialBridgeControl (d := d) (N_c := N_c) k β) K₁ K₂ C hC

end

end YangMills.ClayCore
