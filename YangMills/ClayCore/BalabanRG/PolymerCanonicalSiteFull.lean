import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerCanonicalSite
import YangMills.ClayCore.BalabanRG.PolymerGeometricReadoutFull
import YangMills.ClayCore.BalabanRG.LatticeSiteAdapterFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerCanonicalSiteFull — (v1.0.3-alpha Phase 3)

Canonical bridge on the full (ℤ/2^k ℤ)^d lattice.
Uses canonicalSiteOf (Classical.choose X.nonEmpty) from polymer geometry,
projected via toBalabanFiniteSite to BalabanFiniteSite.

Parallel to PolymerCanonicalSite (simplified BalabanLatticeSite path).
-/

noncomputable section

/-- Canonical physical representative for the full geometry.
    Uses the same canonicalSiteOf as the simplified path. -/
def canonicalPhysicalRepSiteFull (d k : ℕ) : PhysicalPolymerRepSiteFull d k where
  siteOf := canonicalSiteOf

/-- The canonical site in BalabanFiniteSite coordinates. -/
def canonicalBalabanFiniteSite {d k : ℕ} (X : Polymer d (Int.ofNat k)) :
    BalabanFiniteSite d k :=
  toBalabanFiniteSite d k (canonicalSiteOf X)

/-- The canonical full readout at scale 0 from a set of polymers. -/
def canonicalGeometricReadoutFull {d k : ℕ}
    (polys : Finset (Polymer d (Int.ofNat k))) :
    FinitePolymerReadoutFull d k :=
  geometricFiniteReadoutFull (canonicalPhysicalRepSiteFull d k) polys

/-- The canonical full ActivityFieldBridgeFull. -/
def canonicalGeometricBridgeFull {d k : ℕ}
    (polys : Finset (Polymer d (Int.ofNat k))) :
    ActivityFieldBridgeFull d k :=
  bridgeFromFiniteReadoutFull (canonicalGeometricReadoutFull polys)

/-- Zero activity → zero field through canonical full bridge. 0 sorrys. -/
theorem canonicalGeometricBridgeFull_zero {d k : ℕ}
    (polys : Finset (Polymer d (Int.ofNat k))) :
    (canonicalGeometricBridgeFull polys).fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  finiteReadoutFieldFull_zero _

/-- Key identity: canonical full bridge field at canonical site = K(p₀). 0 sorrys. -/
theorem canonicalBridgeFull_field_at_site {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (K : ActivityFamily d k) :
    (canonicalGeometricBridgeFull ({p₀} : Finset (Polymer d (Int.ofNat k)))).fieldOfActivity K
      (canonicalBalabanFiniteSite p₀) =
    K p₀ := by
  -- Use the singleton identity from PolymerGeometricReadoutFull
  have key := singletonFiniteReadoutFieldFull_at_siteOf
    (siteOf := fun p => canonicalBalabanFiniteSite p)
    p₀ K
  simp [canonicalGeometricBridgeFull, canonicalGeometricReadoutFull,
        geometricFiniteReadoutFull, bridgeFromFiniteReadoutFull,
        canonicalPhysicalRepSiteFull, siteOfBalabanFull,
        finiteReadoutFieldFull, canonicalBalabanFiniteSite] at *
  exact key

/-- If K(p₀) ≠ 0, the full canonical bridge field is nonzero. 0 sorrys. -/
theorem canonicalBridgeFull_nonzero {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (K : ActivityFamily d k)
    (hK : K p₀ ≠ 0) :
    (canonicalGeometricBridgeFull ({p₀} : Finset (Polymer d (Int.ofNat k)))).fieldOfActivity K
      (canonicalBalabanFiniteSite p₀) ≠ 0 := by
  rw [canonicalBridgeFull_field_at_site]
  exact hK

/-- The full canonical bridge recovers K(p₀) at the canonical site.
    This is the full-geometry counterpart of canonicalBridgeField_at_site. -/
theorem canonicalBridgeFull_consistent_with_polymer {d k : ℕ}
    (p₀ : Polymer d (Int.ofNat k)) (K : ActivityFamily d k) :
    Polymer.Touches p₀ (canonicalSiteOf p₀) ∧
    (canonicalGeometricBridgeFull ({p₀} : Finset (Polymer d (Int.ofNat k)))).fieldOfActivity K
      (canonicalBalabanFiniteSite p₀) = K p₀ := by
  exact ⟨canonicalSiteOf_touches p₀, canonicalBridgeFull_field_at_site p₀ K⟩

end

end YangMills.ClayCore
