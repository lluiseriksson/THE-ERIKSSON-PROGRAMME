import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerCombinatorics
import YangMills.ClayCore.BalabanRG.PolymerGeometricReadout

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerCanonicalSite — (v1.0.2-alpha Phase 3)

Defines a canonical representative site for each polymer,
chosen from X.sites using Classical.choose.

This is the first physically grounded siteOf: it maps Polymer → LatticeSite d
using the polymer's own geometric support, not an artificial assignment.
-/

noncomputable section

/-- Canonical representative site of a polymer.
    Chosen from X.sites (nonempty by definition). -/
def canonicalSiteOf {d : ℕ} {L : ℤ} (X : Polymer d L) : LatticeSite d :=
  Classical.choose X.nonEmpty

/-- The canonical site lies in X.sites. 0 sorrys. -/
theorem canonicalSiteOf_mem {d : ℕ} {L : ℤ} (X : Polymer d L) :
    canonicalSiteOf X ∈ X.sites :=
  Classical.choose_spec X.nonEmpty

/-- The polymer Touches its canonical site. 0 sorrys. -/
theorem canonicalSiteOf_touches {d : ℕ} {L : ℤ} (X : Polymer d L) :
    Polymer.Touches X (canonicalSiteOf X) :=
  canonicalSiteOf_mem X

/-- The canonical representative physical site.
    Maps each polymer at scale k to its canonical LatticeSite. -/
def canonicalPhysicalRepSite (d k : ℕ) : PhysicalPolymerRepSite d k where
  siteOf := canonicalSiteOf

/-- canonicalPhysicalRepSite touches its canonical site. 0 sorrys. -/
theorem canonicalPhysicalRepSite_touches {d k : ℕ}
    (X : Polymer d (Int.ofNat k)) :
    Polymer.Touches X ((canonicalPhysicalRepSite d k).siteOf X) :=
  canonicalSiteOf_touches X

/-- The canonical bridge from the canonical site assignment.
    First physically grounded bridge derived from polymer geometry. -/
def canonicalGeometricBridge {d k : ℕ} [NeZero d]
    (polys : Finset (Polymer d (Int.ofNat k))) :
    ActivityFieldBridge d k :=
  physicalGeometricBridge (canonicalPhysicalRepSite d k) polys

/-- The canonical RGViaBridgeControl. -/
def canonicalGeometricBridgeControl {d N_c : ℕ} [NeZero d] [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (β : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    RGViaBridgeControl d N_c k β :=
  physicalGeometricBridgeControl k β (canonicalPhysicalRepSite d k) polys

/-- Zero activity → zero field through canonical bridge. 0 sorrys. -/
theorem canonicalGeometricBridge_zero {d k : ℕ} [NeZero d]
    (polys : Finset (Polymer d (Int.ofNat k))) :
    (canonicalGeometricBridge polys).fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  finiteReadoutBridge_zero _

end

end YangMills.ClayCore
