/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceUbarContours
import YangMills.RG.BalabanCMP99PhysicalRegionalAverageTower

/-!
# Source-instantiated physical CMP99 regional scales

This module consumes the literal contour construction from CMP109 (0.12).
The resulting scale package has no free coarse background and no free
`Gamma_1/Gamma_2/Gamma_3`: all four are generated from the fine physical
background and the printed parallel-transport convention.

Only genuinely analytic inputs remain: the scale weight, a small-field
radius, the no-winding inequality, and small-field estimates for the fine
links and for the derived straight coarse transports.  The latter is a
property of the constructed holonomy, not an independently chosen coarse
configuration.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The canonical source-facing scale producer.  Its coarse base field is
the straight fine holonomy `U(c)` and its three contour families are exactly
`c_- -> x`, `[x,x']`, and `x' -> c_+` from CMP109 (0.12). -/
noncomputable def cmp99SourceRegionalScaleData
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (weight epsilon : ℝ)
    (epsilon_nonneg : 0 ≤ epsilon)
    (noWinding : cmp99UbarPhysicalDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(cmp99SourceBaseCoarseBackground background
          (positiveEdgeOfPhysicalBond b) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon) :
    CMP99PhysicalRegionalScaleData Omega background where
  weight := weight
  baseCoarseBackground := cmp99SourceBaseCoarseBackground background
  Γ_1 := cmp99SourceUbarGamma1 (G := SUN Nc)
  Γ_2 := cmp99SourceUbarGamma2 (G := SUN Nc)
  Γ_3 := cmp99SourceUbarGamma3 (G := SUN Nc)
  epsilon := epsilon
  epsilon_nonneg := epsilon_nonneg
  noWinding := noWinding
  fine_small := by
    intro b x hx e he
    exact fine_small e
  coarse_small := coarse_small
  Γ_1_length := by
    intro b x hx
    apply cmp99SourceUbarGamma1_length_le (G := SUN Nc) b x
    simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using hx
  Γ_2_length := by
    intro b x hx
    exact cmp99SourceUbarGamma2_length_le (G := SUN Nc) hd hM b x
  Γ_3_length := by
    intro b x hx
    apply cmp99SourceUbarGamma3_length_le (G := SUN Nc) b x
    simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using hx
  Γ_1_path := by
    intro b x hx
    simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using
      cmp99SourceUbarGamma1_path (G := SUN Nc) b x
        (by simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using hx)
  Γ_1_end := by
    intro b x hx
    simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using
      cmp99SourceUbarGamma1_end (G := SUN Nc) b x
        (by simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using hx)
  Γ_2_path := by
    intro b x hx
    exact cmp99SourceUbarGamma2_path (G := SUN Nc) b x
  Γ_3_path := by
    intro b x hx
    exact cmp99SourceUbarGamma3_path (G := SUN Nc) b x
      (by simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using hx)
  Γ_3_end := by
    intro b x hx
    simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV,
      ConcreteEdge.dstV] using
      cmp99SourceUbarGamma3_end (G := SUN Nc) b x
        (by simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using hx)

/-- A complete source scale packages block saturation with the canonical
physical data, so the tower step consumes one coherent object. -/
structure CMP99SourceRegionalScale
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc)) where
  blockSaturated : Omega.BlockSaturated
  data : CMP99PhysicalRegionalScaleData Omega background

/-- Add one fully packaged source scale to the physical tower. -/
noncomputable def CMP99PhysicalRegionalAverageTower.sourceStep
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (S : CMP99SourceRegionalScale Omega background)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      S.data.nextBackground) :
    CMP99PhysicalRegionalAverageTower rho Omega background :=
  CMP99PhysicalRegionalAverageTower.step rho Omega S.blockSaturated
    background S.data tail

@[simp] theorem CMP99PhysicalRegionalAverageTower.toRegionalAverageTower_sourceStep
    (rho : SUNAdjointModel Nc)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (S : CMP99SourceRegionalScale Omega background)
    (tail : CMP99PhysicalRegionalAverageTower rho
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      S.data.nextBackground) :
    (CMP99PhysicalRegionalAverageTower.sourceStep rho Omega background S tail).toRegionalAverageTower =
      CMP99RegionalAverageTower.step rho Omega S.blockSaturated S.data.weight
        background tail.toRegionalAverageTower :=
  rfl

end

end YangMills.RG
