import Mathlib
import YangMills.ClayCore.BalabanRG.RGViaBridgeFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# RGBridgeCompatibilityFull — (v1.0.4-alpha)

Compatibility layer for the full (ℤ/2^k ℤ)^d geometry.
Re-expresses RGViaBridgeControlFull as skeleton-compatible API.

Parallel to RGBridgeCompatibility (simplified geometry).
-/

noncomputable section

variable {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}

/-- P80 large-field suppression from full bridge control. 0 sorrys. -/
theorem large_field_suppression_from_full_bridge
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  rg_control_full_large_field ctrl K x

/-- P81 Cauchy decay from full bridge control. 0 sorrys. -/
theorem cauchy_decay_from_full_bridge
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  rg_control_full_cauchy ctrl K₁ K₂ x

/-- Combined P80+P81 from full bridge control. 0 sorrys. -/
theorem rg_increment_decay_from_full_bridge
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) :=
  ⟨rg_control_full_large_field ctrl K₁ x, rg_control_full_cauchy ctrl K₁ K₂ x⟩

/-- Zero field from full control. 0 sorrys. -/
theorem zero_field_from_full_bridge
    (ctrl : RGViaBridgeControlFull d N_c k β) :
    ctrl.core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  rg_control_full_zero_field ctrl

end

end YangMills.ClayCore
