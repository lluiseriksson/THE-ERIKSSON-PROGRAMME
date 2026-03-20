import Mathlib
import YangMills.ClayCore.BalabanRG.RGBridgeCompatibilityFiniteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

theorem rg_increment_decay_via_finite_full {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) :=
  ⟨large_field_bound_via_finite_full_control ctrl K₁ x,
   cauchy_bound_via_finite_full_control ctrl K₁ K₂ x⟩

theorem large_field_bound_via_finite_full {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  (rg_increment_decay_via_finite_full ctrl K K x).1

theorem cauchy_bound_via_finite_full {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  (rg_increment_decay_via_finite_full ctrl K₁ K₂ x).2

end

end YangMills.ClayCore
