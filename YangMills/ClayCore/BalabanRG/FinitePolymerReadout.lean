import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerSiteReadout

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# FinitePolymerReadout — (v1.0.1-alpha Phase 2)

Local finite readout: uses a Finset instead of global Fintype(Polymer).
This gives a non-trivial readoutField without requiring the full
polymer Fintype instance.

## Progression
- Phase 1 (PolymerSiteReadout): abstract interface
- Phase 2 (here): finite support, non-trivial field
- Phase 3 (future): physical siteOf from polymer geometry
-/

noncomputable section

/-- A readout with a specified finite set of polymers and a site assignment. -/
structure FinitePolymerReadout (d k : ℕ) where
  polys  : Finset (Polymer d (Int.ofNat k))
  siteOf : Polymer d (Int.ofNat k) → BalabanLatticeSite d k

/-- The induced field: sum K(p) over all polymers in support that map to x. -/
def finiteReadoutField {d k : ℕ} (r : FinitePolymerReadout d k)
    (K : ActivityFamily d k) : BalabanLatticeSite d k → ℝ :=
  fun x => ∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), K p

/-- Zero activity → zero field. 0 sorrys. -/
theorem finiteReadoutField_zero {d k : ℕ} (r : FinitePolymerReadout d k) :
    finiteReadoutField r (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [finiteReadoutField]

/-- Lift to abstract PolymerSiteReadout. 0 sorrys. -/
def toPolymerSiteReadout {d k : ℕ} (r : FinitePolymerReadout d k) :
    PolymerSiteReadout d k where
  readoutField := finiteReadoutField r
  zero_field   := finiteReadoutField_zero r

/-- Lift to ActivityFieldBridge. 0 sorrys. -/
def bridgeFromFiniteReadout {d k : ℕ} (r : FinitePolymerReadout d k) :
    ActivityFieldBridge d k :=
  bridgeFromReadout (toPolymerSiteReadout r)

/-- Zero preserved through finite bridge. 0 sorrys. -/
theorem finiteReadoutBridge_zero {d k : ℕ} (r : FinitePolymerReadout d k) :
    (bridgeFromFiniteReadout r).fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  finiteReadoutField_zero r

/-- Empty support readout: same as zero bridge. 0 sorrys. -/
def emptyFinitePolymerReadout (d k : ℕ)
    (siteOf : Polymer d (Int.ofNat k) → BalabanLatticeSite d k) :
    FinitePolymerReadout d k where
  polys  := ∅
  siteOf := siteOf

/-- Empty readout induces the zero field. 0 sorrys. -/
theorem emptyReadout_zero_field {d k : ℕ}
    (siteOf : Polymer d (Int.ofNat k) → BalabanLatticeSite d k) :
    finiteReadoutField (emptyFinitePolymerReadout d k siteOf) = fun _ _ => 0 := by
  funext K x
  simp [finiteReadoutField, emptyFinitePolymerReadout]

/-- Empty readout bridge = concrete zero bridge. 0 sorrys. -/
theorem emptyReadout_field_eq_concrete {d k : ℕ}
    (siteOf : Polymer d (Int.ofNat k) → BalabanLatticeSite d k) :
    (bridgeFromFiniteReadout (emptyFinitePolymerReadout d k siteOf)).fieldOfActivity =
      (concreteActivityFieldBridge d k).fieldOfActivity := by
  funext K x
  simp [bridgeFromFiniteReadout, toPolymerSiteReadout, bridgeFromReadout,
        finiteReadoutField, emptyFinitePolymerReadout, concreteActivityFieldBridge]


def rgControlFromFiniteReadout {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (r : FinitePolymerReadout d k) :
    RGViaBridgeControl d N_c k β :=
  rg_control_via_bridge k β (bridgeFromFiniteReadout r)

end

end YangMills.ClayCore
