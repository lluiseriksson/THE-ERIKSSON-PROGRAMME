import Mathlib
import YangMills.ClayCore.BalabanRG.P80EstimateViaBridge
import YangMills.ClayCore.BalabanRG.P81EstimateViaBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open ActivityFieldBridge

/-!
# RGViaBridge — Layer 11F (v0.9.11)

Unified control layer for Balaban RG estimates via the geometry bridge.
Packages P80 (large-field suppression) and P81 (Cauchy decay) into a
single API structure.

## Design

`RGViaBridgeControl`: the "contract" any bridge must satisfy.
Once filled, higher layers (P82, P91, LSI) can consume this single object
instead of calling P80/P81 directly.

This layer is ABOVE 15G+15H, BELOW the analytic chain consumers.
-/

noncomputable section

/-- Unified RG control structure via bridge.
    Fields: large_field_bound (P80) + cauchy_bound (P81). -/
structure RGViaBridgeControl (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ) where
  bridge : ActivityFieldBridge d k
  /-- P80: dist(largePart(K), 0) ≤ exp(-β) · dist(K, 0) -/
  large_field_bound : ∀ (K : ActivityFamily d k),
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).largePart
        (bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0)
  /-- P81: dist(largePart(K₁), 0) ≤ C · dist(K₁, K₂) -/
  cauchy_bound : ∀ (K₁ K₂ : ActivityFamily d k) (C : ℝ), 0 ≤ C →
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂

/-- P80 wrapper: large-field suppression. 0 sorrys. -/
theorem rg_large_field_suppression_via_bridge {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridge d k) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K).largePart
        (bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  p80_via_bridge_unified k β bridge K

/-- P81 wrapper: Cauchy decay. 0 sorrys. -/
theorem rg_cauchy_decay_via_bridge {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (bridge : ActivityFieldBridge d k) (K₁ K₂ : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k bridge β K₁).largePart
        (bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  p81_via_bridge_unified k β C hC bridge K₁ K₂

/-- Construct RGViaBridgeControl from any bridge. 0 sorrys. -/
def rg_control_via_bridge {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (bridge : ActivityFieldBridge d k) :
    RGViaBridgeControl d N_c k β :=
  { bridge := bridge,
    large_field_bound := fun K =>
      rg_large_field_suppression_via_bridge k β bridge K,
    cauchy_bound := fun K₁ K₂ C hC =>
      rg_cauchy_decay_via_bridge k β C hC bridge K₁ K₂ }

/-- The control structure is inhabited (by the trivial bridge). 0 sorrys. -/
def trivialBridgeControl {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ) :
    RGViaBridgeControl d N_c k β :=
  rg_control_via_bridge k β
    { fieldOfActivity := fun _ _ => 0,
      zero_field := rfl }

/-- From RGViaBridgeControl, extract the P80 bound for K₁/K₂. -/
theorem rg_control_large_field_bound {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (ctrl : RGViaBridgeControl d N_c k β) (K : ActivityFamily d k) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K).largePart
        (ctrl.bridge.fieldOfActivity K) K)
      (fun _ => 0) ≤
    Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  ctrl.large_field_bound K

/-- From RGViaBridgeControl, extract the P81 Cauchy bound. -/
theorem rg_control_cauchy_bound {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (ctrl : RGViaBridgeControl d N_c k β) (K₁ K₂ : ActivityFamily d k)
    (C : ℝ) (hC : 0 ≤ C) :
    ActivityNorm.dist
      ((selectFieldSplitViaBridge d N_c k ctrl.bridge β K₁).largePart
        (ctrl.bridge.fieldOfActivity K₁) K₁)
      (fun _ => 0) ≤
    C * ActivityNorm.dist K₁ K₂ :=
  ctrl.cauchy_bound K₁ K₂ C hC

end

end YangMills.ClayCore
