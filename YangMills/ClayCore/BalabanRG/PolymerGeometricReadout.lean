import Mathlib
import YangMills.ClayCore.BalabanRG.FinitePolymerReadout
import YangMills.ClayCore.BalabanRG.LatticeSiteAdapter

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerGeometricReadout — (v1.0.2-alpha)

Geometric layer: introduces a site assignment for polymers.

## Design

`PolymerRepresentativeSite`: an abstract assignment Polymer → BalabanLatticeSite.
In P78, this will be the center or bounding-box site of the polymer.
Here it is kept abstract so the API compiles before the P78 geometry is formalized.

## Progression
- Phase 1 (here): abstract PolymerRepresentativeSite interface
- Phase 2 (future): concrete representative from polymer bounding box (P78)
- Phase 3 (future): integrate into main ConcreteActivityFieldBridge
-/

noncomputable section

/-- Abstract assignment of a representative site to each polymer.
    In P78, this is the center of the smallest block containing the polymer. -/
structure PolymerRepresentativeSite (d k : ℕ) where
  /-- Maps each polymer to its representative BalabanLatticeSite. -/
  siteOf : Polymer d (Int.ofNat k) → BalabanLatticeSite d k

/-- Lift a PolymerRepresentativeSite + Finset to a FinitePolymerReadout.
    Geometric version of the polymer readout. -/
def geometricFiniteReadout {d k : ℕ}
    (rep : PolymerRepresentativeSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    FinitePolymerReadout d k where
  polys  := polys
  siteOf := rep.siteOf

/-- The geometric readout field at site x. -/
theorem geometricReadoutField_eq {d k : ℕ}
    (rep : PolymerRepresentativeSite d k)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (K : ActivityFamily d k) (x : BalabanLatticeSite d k) :
    finiteReadoutField (geometricFiniteReadout rep polys) K x =
      ∑ p ∈ polys.filter (fun p => rep.siteOf p = x), K p := rfl

/-- Zero activity → zero geometric readout field. 0 sorrys. -/
theorem geometricReadout_zero {d k : ℕ}
    (rep : PolymerRepresentativeSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    finiteReadoutField (geometricFiniteReadout rep polys) (fun _ => 0) = fun _ => 0 :=
  finiteReadoutField_zero (geometricFiniteReadout rep polys)

/-- The geometric readout induces an ActivityFieldBridge. -/
def geometricBridgeFromRepresentative {d k : ℕ}
    (rep : PolymerRepresentativeSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    ActivityFieldBridge d k :=
  bridgeFromFiniteReadout (geometricFiniteReadout rep polys)

/-- Zero field preserved through geometric bridge. 0 sorrys. -/
theorem geometricBridge_zero {d k : ℕ}
    (rep : PolymerRepresentativeSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    (geometricBridgeFromRepresentative rep polys).fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  geometricReadout_zero rep polys

/-- RGViaBridgeControl from a geometric readout. 0 sorrys. -/
def geometricBridgeControl {d N_c : ℕ} [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (rep : PolymerRepresentativeSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    RGViaBridgeControl d N_c k β :=
  rgControlFromFiniteReadout k β (geometricFiniteReadout rep polys)

/-- The singleton representative site: always returns x₀. -/
def singletonRepresentativeSite {d k : ℕ}
    (x₀ : BalabanLatticeSite d k) : PolymerRepresentativeSite d k where
  siteOf := fun _ => x₀

/-- The singleton representative matches the singleton readout. 0 sorrys. -/
theorem singletonRep_eq_singleton {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (x₀ : BalabanLatticeSite d k) :
    geometricFiniteReadout (singletonRepresentativeSite x₀) {p₀} =
      singletonFinitePolymerReadout p₀ x₀ := rfl


/-! ## Physical representative site -/

/-- A physically grounded representative site.
    siteOf maps Polymer → LatticeSite d (infinite integer lattice).
    Requires [NeZero d] for the BalabanLatticeSite projection. -/
structure PhysicalPolymerRepSite (d k : ℕ) where
  siteOf : Polymer d (Int.ofNat k) → LatticeSite d

/-- Project to BalabanLatticeSite via LatticeSiteAdapter. -/
def siteOfBalaban {d k : ℕ} [NeZero d] (rep : PhysicalPolymerRepSite d k)
    (X : Polymer d (Int.ofNat k)) : BalabanLatticeSite d k :=
  toBalabanSite d k (rep.siteOf X)

/-- Lift to PolymerRepresentativeSite. -/
def toPolymerRepresentativeSite' {d k : ℕ} [NeZero d]
    (rep : PhysicalPolymerRepSite d k) :
    PolymerRepresentativeSite d k where
  siteOf := siteOfBalaban rep

/-- Physical finite readout. -/
def physicalGeometricReadout {d k : ℕ} [NeZero d]
    (rep : PhysicalPolymerRepSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    FinitePolymerReadout d k :=
  geometricFiniteReadout (toPolymerRepresentativeSite' rep) polys

/-- Physical ActivityFieldBridge. -/
def physicalGeometricBridge {d k : ℕ} [NeZero d]
    (rep : PhysicalPolymerRepSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    ActivityFieldBridge d k :=
  bridgeFromFiniteReadout (physicalGeometricReadout rep polys)

/-- Physical RGViaBridgeControl. -/
def physicalGeometricBridgeControl {d N_c : ℕ} [NeZero d] [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (rep : PhysicalPolymerRepSite d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    RGViaBridgeControl d N_c k β :=
  rgControlFromFiniteReadout k β (physicalGeometricReadout rep polys)


end

end YangMills.ClayCore
