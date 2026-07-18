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
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d Nc : ℕ} [NeZero d] [NeZero Nc]

/-- All source data and certificates used at one physical CMP99 scale.  The
path endpoint fields are included even though the tower construction itself
only needs their length bounds: they are the source-faithful data required by
the gauge-covariance theorem for the generated next background. -/
structure CMP99PhysicalRegionalScaleData
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc)) where
  weight : ℝ
  baseCoarseBackground : GaugeConfig d N' (SUN Nc)
  Γ_1 : PhysicalBond d N' → FinBox d (M * N') →
    List (FiniteLatticeGeometry.E (d := d) (N := M * N') (G := SUN Nc))
  Γ_2 : PhysicalBond d N' → FinBox d (M * N') →
    List (FiniteLatticeGeometry.E (d := d) (N := M * N') (G := SUN Nc))
  Γ_3 : PhysicalBond d N' → FinBox d (M * N') →
    List (FiniteLatticeGeometry.E (d := d) (N := M * N') (G := SUN Nc))
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  noWinding : cmp99UbarPhysicalDeviationRadius d M epsilon <
    cmp99UbarNoWindingThreshold Nc
  fine_small : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) →
    ∀ e, (e ∈ Γ_1 b x ∨ e ∈ Γ_2 b x ∨ e ∈ Γ_3 b x) →
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon
  coarse_small : ∀ b,
    ‖(baseCoarseBackground (positiveEdgeOfPhysicalBond b) :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon
  Γ_1_length : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) → (Γ_1 b x).length ≤ d * (M - 1)
  Γ_2_length : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) → (Γ_2 b x).length ≤ d * (M - 1)
  Γ_3_length : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) → (Γ_3 b x).length ≤ d * (M - 1)
  Γ_1_path : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) →
    IsPathFrom
      (blockBasepoint M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b))) (Γ_1 b x)
  Γ_1_end : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) →
    pathEnd
      (blockBasepoint M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b))) (Γ_1 b x) = x
  Γ_2_path : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) → IsPathFrom x (Γ_2 b x)
  Γ_3_path : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) →
    IsPathFrom (pathEnd x (Γ_2 b x)) (Γ_3 b x)
  Γ_3_end : ∀ b x,
    x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)) →
    pathEnd (pathEnd x (Γ_2 b x)) (Γ_3 b x) =
      blockBasepoint M N' (FiniteLatticeGeometry.dst (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b))

/-- The physical background generated for the next scale. -/
noncomputable def CMP99PhysicalRegionalScaleData.nextBackground
    {M N' : ℕ} [NeZero M] [NeZero N']
    {Omega : ActiveGaugeRegion d (M * N')}
    {background : GaugeConfig d (M * N') (SUN Nc)}
    (S : CMP99PhysicalRegionalScaleData Omega background) :
    GaugeConfig d N' (SUN Nc) :=
  cmp99PhysicalUbarGaugeConfig background S.baseCoarseBackground
    S.Γ_1 S.Γ_2 S.Γ_3 S.epsilon S.epsilon_nonneg S.noWinding
    S.fine_small S.coarse_small S.Γ_1_length S.Γ_2_length S.Γ_3_length

/-- A regional tower indexed by the physical background that its head average
must consume.  Its raw constructor is private: outside this module every
inhabitant must be obtained through the source-faithful `stop` or `step` API. -/
structure CMP99PhysicalRegionalAverageTower (rho : SUNAdjointModel Nc)
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N)
    (background : GaugeConfig d N (SUN Nc)) where
  private mk ::
  toRegionalAverageTower : CMP99RegionalAverageTower rho Omega

/-- The zero-step physical tower at a specified background. -/
noncomputable def CMP99PhysicalRegionalAverageTower.stop
    (rho : SUNAdjointModel Nc) {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N)
    (background : GaugeConfig d N (SUN Nc)) :
    CMP99PhysicalRegionalAverageTower rho Omega background where
  toRegionalAverageTower := CMP99RegionalAverageTower.stop rho Omega

/-- Add one source-packaged physical regional average.  The tail is forced to
live over the next background generated by the same scale package. -/
noncomputable def CMP99PhysicalRegionalAverageTower.step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (S : CMP99PhysicalRegionalScaleData Omega background)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      S.nextBackground) :
    CMP99PhysicalRegionalAverageTower rho Omega background where
  toRegionalAverageTower := CMP99RegionalAverageTower.step
    rho Omega hOmega S.weight background tail.toRegionalAverageTower

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
    (background : GaugeConfig d (M * N') (SUN Nc))
    (S : CMP99PhysicalRegionalScaleData Omega background)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      S.nextBackground) :
    (CMP99PhysicalRegionalAverageTower.step rho Omega hOmega background S tail).toRegionalAverageTower =
      CMP99RegionalAverageTower.step rho Omega hOmega S.weight background
        tail.toRegionalAverageTower :=
  rfl

/-- The head is definitionally the regional average in the indexed physical
background and with the packaged source weight. -/
theorem CMP99PhysicalRegionalAverageTower.Qprime_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (S : CMP99PhysicalRegionalScaleData Omega background)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      S.nextBackground) :
    (CMP99PhysicalRegionalAverageTower.step rho Omega hOmega background S tail).toRegionalAverageTower.Qprime =
      tail.toRegionalAverageTower.Qprime.comp
        (cmp99RegionalAverageTowerStep rho Omega S.weight background) :=
  rfl

/-- The exact recursive normalization is inherited from the packaged scale
without an extra background hypothesis. -/
theorem CMP99PhysicalRegionalAverageTower.normalization_step
    (rho : SUNAdjointModel Nc)
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (S : CMP99PhysicalRegionalScaleData Omega background)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      S.nextBackground) :
    (CMP99PhysicalRegionalAverageTower.step rho Omega hOmega background S tail).toRegionalAverageTower.normalization =
      (S.weight ^ 2 * (M : ℝ) ^ d) *
        tail.toRegionalAverageTower.normalization :=
  rfl

end

end YangMills.RG
