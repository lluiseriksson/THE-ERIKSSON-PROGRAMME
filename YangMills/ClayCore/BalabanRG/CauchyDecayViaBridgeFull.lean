import Mathlib
import YangMills.ClayCore.BalabanRG.RGSkeletonViaBridgeFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# CauchyDecayViaBridgeFull — (v1.0.4-alpha)

First high-level consumer on the full (ℤ/2^k ℤ)^d geometry path.
Parallel to CauchyDecayViaBridge (simplified geometry).

Given a RGViaBridgeControlFull, proves both:
- Large-field suppression (P80-style)
- Cauchy decay at any site (P81-style)
-/

noncomputable section

variable {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}

/-- Combined Cauchy decay via full bridge control. 0 sorrys. -/
theorem cauchy_decay_via_full_bridge_control
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) :=
  rg_increment_decay_via_bridge_full ctrl K₁ K₂ x

/-- Consistency: trivial full control (if it exists) recovers skeleton logic. -/
theorem full_bridge_path_recovers_zero_field
    (ctrl : RGViaBridgeControlFull d N_c k β) :
    ctrl.core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  rg_control_full_zero_field ctrl

/-- P80 large-field bound, high-level full API. 0 sorrys. -/
theorem large_field_suppression_high_level_full
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_bound_via_bridge_full ctrl K x

end

end YangMills.ClayCore
