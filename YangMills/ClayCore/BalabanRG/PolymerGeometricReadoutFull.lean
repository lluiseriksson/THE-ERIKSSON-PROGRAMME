import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerCombinatorics
import YangMills.ClayCore.BalabanRG.BalabanFiniteLattice
import YangMills.ClayCore.BalabanRG.LatticeSiteAdapterFull
import YangMills.ClayCore.BalabanRG.ActivitySpaceNorms

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerGeometricReadoutFull — (v1.0.3-alpha Phase 2)

Parallel geometric readout path using the full (ℤ/2^k ℤ)^d lattice geometry.
Uses BalabanFiniteSite d k instead of the simplified BalabanLatticeSite d k.

This is a clean parallel path — does NOT touch the simplified bridge hierarchy.
-/

noncomputable section

/-- Abstract full activity field bridge.
    Field lives on BalabanFiniteSite d k = Fin d → Fin(2^k). -/
structure ActivityFieldBridgeFull (d k : ℕ) where
  fieldOfActivity : ActivityFamily d k → BalabanFiniteSite d k → ℝ
  zero_field : fieldOfActivity (fun _ => 0) = fun _ => 0

/-- Physical representative using full geometry. -/
structure PhysicalPolymerRepSiteFull (d k : ℕ) where
  siteOf : Polymer d (Int.ofNat k) → LatticeSite d

/-- Project to BalabanFiniteSite via LatticeSiteAdapterFull. -/
def siteOfBalabanFull {d k : ℕ} (rep : PhysicalPolymerRepSiteFull d k)
    (X : Polymer d (Int.ofNat k)) : BalabanFiniteSite d k :=
  toBalabanFiniteSite d k (rep.siteOf X)

/-- Finite readout for full geometry. -/
structure FinitePolymerReadoutFull (d k : ℕ) where
  polys  : Finset (Polymer d (Int.ofNat k))
  siteOf : Polymer d (Int.ofNat k) → BalabanFiniteSite d k

/-- The induced field on BalabanFiniteSite: sum K(p) over polys at x. -/
def finiteReadoutFieldFull {d k : ℕ} (r : FinitePolymerReadoutFull d k)
    (K : ActivityFamily d k) : BalabanFiniteSite d k → ℝ :=
  fun x => ∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), K p

/-- Zero activity → zero field. 0 sorrys. -/
theorem finiteReadoutFieldFull_zero {d k : ℕ} (r : FinitePolymerReadoutFull d k) :
    finiteReadoutFieldFull r (fun _ => 0) = fun _ => 0 := by
  funext x; simp [finiteReadoutFieldFull]

/-- Lift FinitePolymerReadoutFull to ActivityFieldBridgeFull. -/
def bridgeFromFiniteReadoutFull {d k : ℕ} (r : FinitePolymerReadoutFull d k) :
    ActivityFieldBridgeFull d k where
  fieldOfActivity := finiteReadoutFieldFull r
  zero_field      := finiteReadoutFieldFull_zero r

/-- Geometric readout from a physical representative. -/
def geometricFiniteReadoutFull {d k : ℕ}
    (rep : PhysicalPolymerRepSiteFull d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    FinitePolymerReadoutFull d k where
  polys  := polys
  siteOf := siteOfBalabanFull rep

/-- Full geometric ActivityFieldBridgeFull. -/
def geometricBridgeFull {d k : ℕ}
    (rep : PhysicalPolymerRepSiteFull d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    ActivityFieldBridgeFull d k :=
  bridgeFromFiniteReadoutFull (geometricFiniteReadoutFull rep polys)

/-- Zero activity through geometric bridge. 0 sorrys. -/
theorem geometricBridgeFull_zero {d k : ℕ}
    (rep : PhysicalPolymerRepSiteFull d k)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    (geometricBridgeFull rep polys).fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  finiteReadoutFieldFull_zero _

/-- Singleton readout field identity for full geometry. 0 sorrys. -/
theorem singletonFiniteReadoutFieldFull_at_siteOf {d k : ℕ}
    (siteOf : Polymer d (Int.ofNat k) → BalabanFiniteSite d k)
    (p₀ : Polymer d (Int.ofNat k)) (K : ActivityFamily d k) :
    finiteReadoutFieldFull
      ({ polys := {p₀}, siteOf := siteOf } : FinitePolymerReadoutFull d k)
      K (siteOf p₀) = K p₀ := by
  unfold finiteReadoutFieldFull
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
