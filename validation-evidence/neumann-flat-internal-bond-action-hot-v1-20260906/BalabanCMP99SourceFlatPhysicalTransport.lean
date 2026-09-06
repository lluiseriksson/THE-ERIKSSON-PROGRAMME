/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower

/-!
# Flat physical contour transport

The physical CMP99 average does not receive a transport family from its
caller: it constructs contour holonomies in the supplied background and then
uses their adjoint action.  This module specializes that construction to the
literal flat gauge configuration.  Every ordered Wilson line is then one, so
the physical transport is the identity, the average is the normalized block
sum, and the source weighted adjoint is unit synthesis.

Honest scope: this is the exact flat-background specialization on an arbitrary
block-saturated active region.  It does not construct a Fourier transform,
identify the interacting transport with the flat one, diagonalize the active
regional precision, construct an inverse, or produce a regional Green bound.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The literal flat gauge configuration: every oriented link is the group
identity. -/
def cmp99SourceFlatGaugeConfig (d N Nc : ℕ)
    [NeZero d] [NeZero N] [NeZero Nc] :
    GaugeConfig d N (SUN Nc) where
  toFun := fun _ => 1
  map_reverse := by intro _; simp

@[simp] theorem cmp99SourceFlatGaugeConfig_apply
    (e : FiniteLatticeGeometry.E (d := d) (N := M * N') (G := SUN Nc)) :
    cmp99SourceFlatGaugeConfig d (M * N') Nc e = 1 := rfl

/-- Every ordered Wilson line in the literal flat background is one. -/
@[simp] theorem wilsonLine_cmp99SourceFlatGaugeConfig
    (es : List
      (FiniteLatticeGeometry.E (d := d) (N := M * N') (G := SUN Nc))) :
    wilsonLine (cmp99SourceFlatGaugeConfig d (M * N') Nc) es = 1 := by
  induction es with
  | nil => simp
  | cons e es ih =>
      rw [wilsonLine_cons, cmp99SourceFlatGaugeConfig_apply, ih, one_mul]

/-- Consequently every literal CMP99 contour has trivial holonomy in the flat
background, independently of the chosen path. -/
@[simp] theorem cmp99ContourHolonomy_flat
    (Gamma : CMP99ContourSystem d M N' (SUN Nc))
    (y : FinBox d N') (x : FinBox d (M * N')) :
    cmp99ContourHolonomy Gamma
        (cmp99SourceFlatGaugeConfig d (M * N') Nc) y x = 1 := by
  unfold cmp99ContourHolonomy OrientedLatticePath.holonomy
  exact wilsonLine_cmp99SourceFlatGaugeConfig (Gamma y x).edges

/-- The source-constructed physical transport is literally the identity in
the flat background. -/
@[simp] theorem cmp99SourceWeightedPhysicalTransport_flat_apply
    (rho : SUNAdjointModel Nc) (y : FinBox d N')
    (x : FinBox d (M * N')) (X : SUNLieCoord Nc) :
    cmp99SourceWeightedPhysicalTransport rho
        (cmp99SourceFlatGaugeConfig d (M * N') Nc) y x X = X := by
  unfold cmp99SourceWeightedPhysicalTransport cmp99AdjointBlockTransport
  rw [cmp99ContourHolonomy_flat]
  exact rho.ad_one_apply X

/-- Equality of the full fibre isometry, not merely equality after one
selected vector. -/
theorem cmp99SourceWeightedPhysicalTransport_flat_eq_refl
    (rho : SUNAdjointModel Nc) (y : FinBox d N')
    (x : FinBox d (M * N')) :
    cmp99SourceWeightedPhysicalTransport rho
        (cmp99SourceFlatGaugeConfig d (M * N') Nc) y x =
      LinearIsometryEquiv.refl ℝ (SUNLieCoord Nc) := by
  apply LinearIsometryEquiv.ext
  intro X
  exact cmp99SourceWeightedPhysicalTransport_flat_apply rho y x X

/-- In the flat background the physical one-step average is exactly its
source-normalized block sum. -/
theorem cmp99SourceTransportedBlockAverageCLM_flat_apply
    (Omega : ActiveGaugeRegion d (M * N')) (rho : SUNAdjointModel Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)) phi y =
      cmp99SourceBlockAverageWeight M d •
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
        phi (cmp99ActiveFineSiteOfBlock Omega y x) := by
  rw [cmp99SourceTransportedBlockAverageCLM,
    cmp99TransportedBlockAverageCLM_apply]
  apply congrArg (fun Z => cmp99SourceBlockAverageWeight M d • Z)
  apply Finset.sum_congr rfl
  intro x _
  rw [cmp99SourceWeightedPhysicalTransport_flat_apply]

/-- The printed source weighted adjoint reduces to unit-coefficient synthesis
in the same flat background. -/
theorem cmp99SourceTransportedBlockWeightedAdjointCLM_flat_apply
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (rho : SUNAdjointModel Nc)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) (x : ActiveGaugeRegion.Site Omega) :
    cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
        (cmp99SourceWeightedPhysicalTransport rho
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)) eta x =
      eta ⟨blockSite M N' x.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega (blockSite M N' x.1)).2
            (hOmega x.1 x.2)⟩ := by
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM,
    cmp99TransportedBlockSynthesisCLM_apply]
  rw [cmp99SourceWeightedPhysicalTransport_flat_eq_refl]
  simp only [one_smul]
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using
    (LinearIsometryEquiv.symm_apply_apply
      (LinearIsometryEquiv.refl ℝ (SUNLieCoord Nc))
      (eta ⟨blockSite M N' x.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega (blockSite M N' x.1)).2
            (hOmega x.1 x.2)⟩))

end

end YangMills.RG
