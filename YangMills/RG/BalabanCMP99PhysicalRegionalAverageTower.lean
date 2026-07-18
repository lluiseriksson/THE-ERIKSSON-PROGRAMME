/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalUbarGaugeConfig
import YangMills.RG.BalabanCMP99RegionalAverageTower

/-!
# A background-faithful physical CMP99 regional tower

This module removes the arbitrary `background` argument from recursive uses of
`CMP99RegionalAverageTower.step`.  A physical tower is indexed by its actual
group-valued background.  At a nonterminal node, its tail is indexed by the
literal physical `Ubar` configuration constructed from that background and
the printed coarse base background.  Consequently the next averaging step
cannot silently be supplied with a different gauge configuration.

The coarse base background, contour systems, and their physical certificates
remain explicit source data.  The result does not pretend that the printed
coarse base is determined by the fine background alone.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d Nc : ℕ} [NeZero d] [NeZero Nc]

/-- A regional tower indexed by the physical background that its head average
must consume.  The index is propagated recursively by `step`. -/
structure CMP99PhysicalRegionalAverageTower (rho : SUNAdjointModel Nc)
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N)
    (background : GaugeConfig d N (SUN Nc)) where
  toRegionalAverageTower : CMP99RegionalAverageTower rho Omega

/-- The zero-step physical tower at a specified background. -/
noncomputable def CMP99PhysicalRegionalAverageTower.stop
    (rho : SUNAdjointModel Nc) {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N)
    (background : GaugeConfig d N (SUN Nc)) :
    CMP99PhysicalRegionalAverageTower rho Omega background where
  toRegionalAverageTower := CMP99RegionalAverageTower.stop rho Omega

/-- Add one physical regional average.  The head factor uses the background
in the result index, while the tail is indexed by the literal physical Ubar
configuration produced at this step. -/
noncomputable def CMP99PhysicalRegionalAverageTower.step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (baseCoarseBackground : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' →
      FinBox d (M * N') →
        List (FiniteLatticeGeometry.E
          (d := d) (N := M * N') (G := SUN Nc)))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d M ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hΓ1) (hΓ2) (hΓ3)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (cmp99PhysicalUbarGaugeConfig background baseCoarseBackground
        Γ_1 Γ_2 Γ_3 ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3)) :
    CMP99PhysicalRegionalAverageTower rho Omega background where
  toRegionalAverageTower := CMP99RegionalAverageTower.step
    rho Omega hOmega w background tail.toRegionalAverageTower

@[simp] theorem CMP99PhysicalRegionalAverageTower.toRegionalAverageTower_stop
    (rho : SUNAdjointModel Nc) {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N)
    (background : GaugeConfig d N (SUN Nc)) :
    (CMP99PhysicalRegionalAverageTower.stop rho Omega background).toRegionalAverageTower =
      CMP99RegionalAverageTower.stop rho Omega :=
  rfl

@[simp] theorem CMP99PhysicalRegionalAverageTower.toRegionalAverageTower_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (baseCoarseBackground : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' →
      FinBox d (M * N') →
        List (FiniteLatticeGeometry.E
          (d := d) (N := M * N') (G := SUN Nc)))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d M ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hΓ1) (hΓ2) (hΓ3)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (cmp99PhysicalUbarGaugeConfig background baseCoarseBackground
        Γ_1 Γ_2 Γ_3 ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3)) :
    (CMP99PhysicalRegionalAverageTower.step rho Omega hOmega w background
      baseCoarseBackground Γ_1 Γ_2 Γ_3 ε hε hsmall
      hfine hcoarse hΓ1 hΓ2 hΓ3 tail).toRegionalAverageTower =
      CMP99RegionalAverageTower.step rho Omega hOmega w background
        tail.toRegionalAverageTower :=
  rfl

/-- The head of a physical recursive step is definitionally the regional
average in the current physical background. -/
theorem CMP99PhysicalRegionalAverageTower.Qprime_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (baseCoarseBackground : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' →
      FinBox d (M * N') →
        List (FiniteLatticeGeometry.E
          (d := d) (N := M * N') (G := SUN Nc)))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d M ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hΓ1) (hΓ2) (hΓ3)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (cmp99PhysicalUbarGaugeConfig background baseCoarseBackground
        Γ_1 Γ_2 Γ_3 ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3)) :
    (CMP99PhysicalRegionalAverageTower.step rho Omega hOmega w background
      baseCoarseBackground Γ_1 Γ_2 Γ_3 ε hε hsmall
      hfine hcoarse hΓ1 hΓ2 hΓ3 tail).toRegionalAverageTower.Qprime =
      tail.toRegionalAverageTower.Qprime.comp
        (cmp99RegionalAverageTowerStep rho Omega w background) :=
  rfl

/-- The exact recursive normalization is inherited without an extra
background hypothesis. -/
theorem CMP99PhysicalRegionalAverageTower.normalization_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (w : ℝ)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (baseCoarseBackground : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' →
      FinBox d (M * N') →
        List (FiniteLatticeGeometry.E
          (d := d) (N := M * N') (G := SUN Nc)))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : cmp99UbarPhysicalDeviationRadius d M ε <
      cmp99UbarNoWindingThreshold Nc)
    (hfine) (hcoarse) (hΓ1) (hΓ2) (hΓ3)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (cmp99PhysicalUbarGaugeConfig background baseCoarseBackground
        Γ_1 Γ_2 Γ_3 ε hε hsmall hfine hcoarse hΓ1 hΓ2 hΓ3)) :
    (CMP99PhysicalRegionalAverageTower.step rho Omega hOmega w background
      baseCoarseBackground Γ_1 Γ_2 Γ_3 ε hε hsmall
      hfine hcoarse hΓ1 hΓ2 hΓ3 tail).toRegionalAverageTower.normalization =
      (w ^ 2 * (M : ℝ) ^ d) *
        tail.toRegionalAverageTower.normalization :=
  rfl

end

end YangMills.RG
