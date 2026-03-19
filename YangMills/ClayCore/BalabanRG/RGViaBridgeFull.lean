import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerGeometricReadoutFull
import YangMills.ClayCore.BalabanRG.PolymerCanonicalSiteFull
import YangMills.ClayCore.BalabanRG.ActivitySpaceNorms
import YangMills.ClayCore.BalabanRG.RGContractionRate

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# RGViaBridgeFull — (v1.0.4-alpha)

Unified RG control for the full (ℤ/2^k ℤ)^d geometry.

## Three-layer design

1. Core (no ActivityNorm): bridge + zero_activity → zero_field
2. Named Prop hypotheses: P80 + P81 analytic bounds (formal debt)
3. Full package: core + hypotheses
-/

noncomputable section

/-! ## Layer 1: Core (no ActivityNorm required) -/

/-- Core: bridge + zero_activity→zero_field.
    No ActivityNorm needed here. -/
structure RGViaBridgeControlFullCore (d N_c : ℕ) [NeZero N_c] (k : ℕ) where
  bridge : ActivityFieldBridgeFull d k
  zero_activity_zero_field :
    bridge.fieldOfActivity (fun _ => 0) = fun _ => 0

/-- Extract field function from core. -/
def RGViaBridgeControlFullCore.fieldOf {d N_c : ℕ} [NeZero N_c] {k : ℕ}
    (ctrl : RGViaBridgeControlFullCore d N_c k) :
    ActivityFamily d k → BalabanFiniteSite d k → ℝ :=
  ctrl.bridge.fieldOfActivity

/-- Canonical geometric bridge satisfies core. 0 sorrys. -/
def canonicalGeometricBridgeControlFullCore {d N_c : ℕ} [NeZero N_c]
    (k : ℕ) (polys : Finset (Polymer d (Int.ofNat k))) :
    RGViaBridgeControlFullCore d N_c k where
  bridge := canonicalGeometricBridgeFull polys
  zero_activity_zero_field := canonicalGeometricBridgeFull_zero polys

/-- Zero field through canonical core. 0 sorrys. -/
theorem canonicalCore_zero_field {d N_c : ℕ} [NeZero N_c]
    (k : ℕ) (polys : Finset (Polymer d (Int.ofNat k))) :
    (canonicalGeometricBridgeControlFullCore (d := d) (N_c := N_c) k polys).bridge.fieldOfActivity
        (fun _ => 0) = fun _ => 0 := by
  let ctrl : RGViaBridgeControlFullCore d N_c k :=
    canonicalGeometricBridgeControlFullCore (d := d) (N_c := N_c) k polys
  simpa [ctrl] using ctrl.zero_activity_zero_field

/-! ## Layer 2: Named analytic hypotheses (formal debt) -/

/-- P80-style suppression bound. Analytic content: deferred. -/
def FullLargeFieldSuppressionBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridgeFull d k) : Prop :=
  ∀ (K : ActivityFamily d k) (x : BalabanFiniteSite d k),
    |bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0)

/-- P81-style Cauchy summability bound. Analytic content: deferred. -/
def FullCauchySummabilityBound (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridgeFull d k) : Prop :=
  ∀ (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k),
    |bridge.fieldOfActivity K₁ x - bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂

/-! ## Layer 3: Full control package -/

/-- Full RG control: core + analytic bounds.
    When analytic hypotheses are proved, all fields of this become theorems. -/
structure RGViaBridgeControlFull (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ) where
  core : RGViaBridgeControlFullCore d N_c k
  large_field_bound :
    FullLargeFieldSuppressionBound d N_c k β core.bridge
  cauchy_bound :
    FullCauchySummabilityBound d N_c k β core.bridge

/-- Extract large-field bound from full control. 0 sorrys. -/
theorem rg_control_full_large_field {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  ctrl.large_field_bound K x

/-- Extract Cauchy bound from full control. 0 sorrys. -/
theorem rg_control_full_cauchy {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  ctrl.cauchy_bound K₁ K₂ x

/-- Zero field from full control. 0 sorrys. -/
theorem rg_control_full_zero_field {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} {β : ℝ}
    (ctrl : RGViaBridgeControlFull d N_c k β) :
    ctrl.core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  ctrl.core.zero_activity_zero_field

end

end YangMills.ClayCore
