import Mathlib
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionFinite

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

noncomputable section

theorem large_field_bound_via_finite_full_control {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  rg_control_full_large_field ctrl K x

theorem cauchy_bound_via_finite_full_control {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  rg_control_full_cauchy ctrl K₁ K₂ x

theorem zero_field_via_finite_full_control {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β) :
    ctrl.core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  rg_control_full_zero_field ctrl

def finiteControlFromFiniteHypotheses {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (hlarge : FiniteFullLargeFieldBound d N_c k β polys)
    (hcauchy : FiniteFullCauchyBound d N_c k β polys) :
    RGViaBridgeControlFull d N_c k β :=
  finiteCanonicalGeometricBridgeControlFull k β polys hlarge hcauchy

end

end YangMills.ClayCore
