import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanFieldSpace
import YangMills.ClayCore.BalabanRG.ActivitySpaceNorms
import YangMills.ClayCore.BalabanRG.ActivityFieldBridge
import YangMills.ClayCore.BalabanRG.ConcreteActivityFieldBridge

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerSiteReadout — (v1.0.1-alpha)

Phase 1: abstract readout interface, avoiding Fintype(Polymer) constraints.

A PolymerSiteReadout packages the induced field directly as data.
The combinatorial sum will be the concrete readoutField in Phase 2,
once Polymer Fintype instances are available.
-/

noncomputable section

/-- Abstract polymer site readout.
    Stores the induced field as a function, avoiding Fintype requirements. -/
structure PolymerSiteReadout (d k : ℕ) where
  readoutField : ActivityFamily d k → BalabanLatticeSite d k → ℝ
  zero_field   : readoutField (fun _ => 0) = fun _ => 0

/-- Trivial readout: zero field for every activity. -/
def trivialPolymerSiteReadout (d k : ℕ) : PolymerSiteReadout d k where
  readoutField := fun _ _ => 0
  zero_field   := rfl

/-- The readout induces an ActivityFieldBridge. 0 sorrys. -/
def bridgeFromReadout {d k : ℕ} (r : PolymerSiteReadout d k) :
    ActivityFieldBridge d k where
  fieldOfActivity := r.readoutField
  zero_field      := r.zero_field

/-- Zero field preserved through the bridge. 0 sorrys. -/
theorem readoutBridge_zero {d k : ℕ} (r : PolymerSiteReadout d k) :
    (bridgeFromReadout r).fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  r.zero_field

/-- The trivial readout induces the concrete zero bridge. 0 sorrys. -/
theorem trivial_readout_bridge_eq {d k : ℕ} :
    bridgeFromReadout (trivialPolymerSiteReadout d k) =
      concreteActivityFieldBridge d k := rfl

/-- Any readout yields an RGViaBridgeControl. -/
def rgControlFromReadout {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] {k : ℕ} (β : ℝ)
    (r : PolymerSiteReadout d k) :
    RGViaBridgeControl d N_c k β :=
  rg_control_via_bridge k β (bridgeFromReadout r)

/-- The trivial readout gives the same control as trivialBridgeControl. 0 sorrys. -/
theorem trivial_readout_control_eq {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ) :
    rgControlFromReadout (d := d) (N_c := N_c) β
      (trivialPolymerSiteReadout d k) =
    trivialBridgeControl (d := d) (N_c := N_c) k β := by
  unfold rgControlFromReadout trivialBridgeControl
  rw [trivial_readout_bridge_eq]
  rfl

end

end YangMills.ClayCore
