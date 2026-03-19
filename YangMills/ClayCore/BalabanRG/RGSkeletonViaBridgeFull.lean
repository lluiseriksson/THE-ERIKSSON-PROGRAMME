import Mathlib
import YangMills.ClayCore.BalabanRG.RGBridgeCompatibilityFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# RGSkeletonViaBridgeFull — (v1.0.4-alpha)

Facade layer for the full (ℤ/2^k ℤ)^d geometry.
Exposes skeleton-style API backed by the full bridge control.

Parallel to RGSkeletonViaBridge (simplified geometry).
-/

noncomputable section

variable {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}

/-- P80 suppression from full control, skeleton-style API. 0 sorrys. -/
theorem large_field_bound_via_bridge_full
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_suppression_from_full_bridge ctrl K x

/-- P81 Cauchy decay from full control, skeleton-style API. 0 sorrys. -/
theorem cauchy_bound_via_bridge_full
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  cauchy_decay_from_full_bridge ctrl K₁ K₂ x

/-- Combined full RG increment decay. 0 sorrys. -/
theorem rg_increment_decay_via_bridge_full
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) :=
  rg_increment_decay_from_full_bridge ctrl K₁ K₂ x

end

end YangMills.ClayCore
