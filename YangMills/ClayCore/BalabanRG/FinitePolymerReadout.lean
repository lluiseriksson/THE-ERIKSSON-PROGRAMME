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


/-! ## Phase 3: Singleton readout — first non-trivial bridge -/

/-- Singleton readout: one polymer p₀ routed to one site x₀. -/
def singletonFinitePolymerReadout {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k) :
    FinitePolymerReadout d k where
  polys  := {p₀}
  siteOf := fun _ => x₀

/-- The singleton readout field at x₀ equals K(p₀). 0 sorrys. -/
theorem singletonReadoutField_at_center {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k)
    (K : ActivityFamily d k) :
    finiteReadoutField (singletonFinitePolymerReadout p₀ x₀) K x₀ = K p₀ := by
  simp [finiteReadoutField, singletonFinitePolymerReadout]

/-- The singleton readout field at x ≠ x₀ is 0. 0 sorrys. -/
theorem singletonReadoutField_away {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k)
    {x : BalabanLatticeSite d k} (hx : x ≠ x₀)
    (K : ActivityFamily d k) :
    finiteReadoutField (singletonFinitePolymerReadout p₀ x₀) K x = 0 := by
  simp [finiteReadoutField, singletonFinitePolymerReadout, hx.symm]

/-- First non-trivial ActivityFieldBridge.
    K(p₀) appears at site x₀; zero elsewhere. -/
def singletonBridge {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k) :
    ActivityFieldBridge d k :=
  bridgeFromFiniteReadout (singletonFinitePolymerReadout p₀ x₀)

/-- The singleton bridge is not the zero bridge when K(p₀) ≠ 0. -/
theorem singletonBridge_fieldOfActivity_at {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k)
    (K : ActivityFamily d k) :
    (singletonBridge p₀ x₀).fieldOfActivity K x₀ = K p₀ :=
  singletonReadoutField_at_center p₀ x₀ K

/-- RGViaBridgeControl from the singleton bridge. 0 sorrys. -/
def singletonBridgeControl {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k) :
    RGViaBridgeControl d N_c k β :=
  rgControlFromFiniteReadout k β (singletonFinitePolymerReadout p₀ x₀)



/-- The singleton bridge field at x₀ is K(p₀). Explicit non-triviality. -/
theorem singletonBridge_field_at_center {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k)
    (K : ActivityFamily d k) :
    (singletonBridge p₀ x₀).fieldOfActivity K x₀ = K p₀ :=
  singletonReadoutField_at_center p₀ x₀ K

/-- If K(p₀) ≠ 0, the singleton bridge field at x₀ is nonzero.
    This is the first proof that the bridge is genuinely non-trivial. 0 sorrys. -/
theorem singletonBridge_nonzero_of_activity_nonzero {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k)
    (K : ActivityFamily d k) (hK : K p₀ ≠ 0) :
    (singletonBridge p₀ x₀).fieldOfActivity K x₀ ≠ 0 := by
  rw [singletonBridge_field_at_center]
  exact hK



/-- Generic singleton readout field identity.
    The field value at siteOf(p₀) from a singleton readout is K(p₀). 0 sorrys. -/
theorem singletonFiniteReadoutField_at_siteOf {d k : ℕ}
    (siteOf : Polymer d (Int.ofNat k) → BalabanLatticeSite d k)
    (p₀ : Polymer d (Int.ofNat k)) (K : ActivityFamily d k) :
    finiteReadoutField
      ({ polys := {p₀}, siteOf := siteOf } : FinitePolymerReadout d k)
      K (siteOf p₀) = K p₀ := by
  unfold finiteReadoutField
  have hfilter : ({p₀} : Finset (Polymer d (Int.ofNat k))).filter
      (fun p => siteOf p = siteOf p₀) = {p₀} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, _⟩; rfl
    · rintro rfl; exact ⟨rfl, rfl⟩
  rw [hfilter]
  simp


end

end YangMills.ClayCore
