import Mathlib
import YangMills.ClayCore.BalabanRG.RGSkeletonViaBridgeFiniteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

theorem cauchy_decay_via_finite_full_bridge_control {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) :=
  rg_increment_decay_via_finite_full ctrl K₁ K₂ x

theorem large_field_suppression_finite_full_consumer {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  large_field_bound_via_finite_full ctrl K x

theorem cauchy_summability_finite_full_consumer {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  cauchy_bound_via_finite_full ctrl K₁ K₂ x

theorem finite_full_bridge_control_from_hypotheses {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (hlarge : FiniteFullLargeFieldBound d N_c k β polys)
    (hcauchy : FiniteFullCauchyBound d N_c k β polys)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    let ctrl := finiteControlFromFiniteHypotheses (d := d) (N_c := N_c) k β polys hlarge hcauchy
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) := by
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end

end YangMills.ClayCore
