/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceUbarContours
import YangMills.RG.BalabanCMP99PhysicalRegionalAverageTower
import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint

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

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-! ## Small field propagated to the derived coarse transport -/

/-- The source-facing no-winding radius when only a fine-link radius is
given.  The three block contours contribute `3 d (M - 1)` links and the
derived straight coarse transport contributes exactly `M` more links. -/
def cmp99SourceUbarFineDeviationRadius (d M : ℕ) (epsilonFine : ℝ) : ℝ :=
  ((3 * d * (M - 1) + M : ℕ) : ℝ) * epsilonFine

/-- The straight coarse background inherits the exact path-length bound
`M * epsilonFine` from uniform fine-link smallness. -/
theorem norm_cmp99SourceBaseCoarseBackground_sub_one_le
    (background : GaugeConfig d (M * N') (SUN Nc))
    (epsilonFine : ℝ)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (b : PhysicalBond d N') :
    ‖(cmp99SourceBaseCoarseBackground background
        (positiveEdgeOfPhysicalBond b) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      (M : ℝ) * epsilonFine := by
  rw [cmp99SourceBaseCoarseBackground_apply_pos]
  change
    ‖((wilsonLine background
        (cmp99SourceParallelTransportPath (G := SUN Nc)
          (blockBasepoint M N' b.1) b.2).edges : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      (M : ℝ) * epsilonFine
  simpa only [cmp99SourceParallelTransportPath_length] using
    norm_wilsonLine_sub_one_le_length_mul background
      (cmp99SourceParallelTransportPath (G := SUN Nc)
        (blockBasepoint M N' b.1) b.2).edges epsilonFine
      (fun e _ => fine_small e)

/-- The literal CMP109 deviation is controlled directly by the fine-link
radius, with no separately supplied coarse-field estimate. -/
theorem norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖UbarDeviationLogArg
        (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        background (cmp99SourceBaseCoarseBackground background)
        (positiveEdgeOfPhysicalBond b) x
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤
      cmp99SourceUbarFineDeviationRadius d M epsilonFine := by
  let Gamma1 : FinBox d (M * N') → List (ConcreteEdge d (M * N')) :=
    cmp99SourceUbarGamma1 (G := SUN Nc) b
  let Gamma2 : FinBox d (M * N') → List (ConcreteEdge d (M * N')) :=
    cmp99SourceUbarGamma2 (G := SUN Nc) b
  let Gamma3 : FinBox d (M * N') → List (ConcreteEdge d (M * N')) :=
    cmp99SourceUbarGamma3 (G := SUN Nc) b
  have h1 := norm_wilsonLine_sub_one_le_length_mul background
    (Gamma1 x) epsilonFine (fun e _ => fine_small e)
  have h2 := norm_wilsonLine_sub_one_le_length_mul background
    (Gamma2 x) epsilonFine (fun e _ => fine_small e)
  have h3 := norm_wilsonLine_sub_one_le_length_mul background
    (Gamma3 x) epsilonFine (fun e _ => fine_small e)
  have hc := norm_cmp99SourceBaseCoarseBackground_sub_one_le
    background epsilonFine fine_small b
  have hGamma1 : (Gamma1 x).length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma1_length_le (G := SUN Nc) b x hx
  have hGamma2 : (Gamma2 x).length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma2_length_le (G := SUN Nc) hd hM b x
  have hGamma3 : (Gamma3 x).length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma3_length_le (G := SUN Nc) b x hx
  calc
    _ ≤ ‖((wilsonLine background (Gamma1 x) : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖((wilsonLine background (Gamma2 x) : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖((wilsonLine background (Gamma3 x) : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖(cmp99SourceBaseCoarseBackground background
            (positiveEdgeOfPhysicalBond b) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ :=
      norm_UbarDeviationLogArg_le_four_factors
        background (cmp99SourceBaseCoarseBackground background)
        (positiveEdgeOfPhysicalBond b) x Gamma1 Gamma2 Gamma3
    _ ≤ ((Gamma1 x).length : ℝ) * epsilonFine +
        ((Gamma2 x).length : ℝ) * epsilonFine +
        ((Gamma3 x).length : ℝ) * epsilonFine +
        (M : ℝ) * epsilonFine := by gcongr
    _ ≤ ((d * (M - 1) : ℕ) : ℝ) * epsilonFine +
        ((d * (M - 1) : ℕ) : ℝ) * epsilonFine +
        ((d * (M - 1) : ℕ) : ℝ) * epsilonFine +
        (M : ℝ) * epsilonFine := by
      gcongr
    _ = cmp99SourceUbarFineDeviationRadius d M epsilonFine := by
      simp only [cmp99SourceUbarFineDeviationRadius, Nat.cast_add,
        Nat.cast_mul]
      ring

/-- The sharp source radius canonically produces the no-winding budget. -/
noncomputable def cmp99SourceUbarFineNoWindingBudget
    (epsilonFine : ℝ)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc) :
    MatrixNearLogNoWindingBudget Nc :=
  cmp99PhysicalNoWindingBudget
    (cmp99SourceUbarFineDeviationRadius d M epsilonFine) noWinding

@[simp] theorem cmp99SourceUbarFineNoWindingBudget_delta
    (epsilonFine : ℝ)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc) :
    (cmp99SourceUbarFineNoWindingBudget
      (d := d) (M := M) (Nc := Nc) epsilonFine noWinding).δ =
      cmp99SourceUbarFineDeviationRadius d M epsilonFine := by
  simp [cmp99SourceUbarFineNoWindingBudget, cmp99PhysicalNoWindingBudget]

/-- The canonical geometric scale producer from a direct deviation budget.
Its coarse base field is the straight fine holonomy `U(c)` and its three
contour families are exactly `c_- -> x`, `[x,x']`, and `x' -> c_+` from
CMP109 (0.12). -/
noncomputable def cmp99SourceRegionalScaleDataOfDeviationBudget
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (weight : ℝ) (deviationBudget : MatrixNearLogNoWindingBudget Nc)
    (deviation_bound : ∀ b : PhysicalBond d N',
      ∀ x : FinBox d (M * N'), x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          background (cmp99SourceBaseCoarseBackground background)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ deviationBudget.δ) :
    CMP99PhysicalRegionalScaleData Omega background where
  weight := weight
  baseCoarseBackground := cmp99SourceBaseCoarseBackground background
  Γ_1 := cmp99SourceUbarGamma1 (G := SUN Nc)
  Γ_2 := cmp99SourceUbarGamma2 (G := SUN Nc)
  Γ_3 := cmp99SourceUbarGamma3 (G := SUN Nc)
  deviationBudget := deviationBudget
  deviation_bound := by
    intro b x hx
    exact deviation_bound b x
      (by simpa [positiveEdgeOfPhysicalBond, ConcreteEdge.srcV] using hx)
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

/-- The original common-radius source producer, retained as a convenient
corollary of the sharper direct-budget interface. -/
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
    CMP99PhysicalRegionalScaleData Omega background :=
  cmp99SourceRegionalScaleDataOfDeviationBudget hd hM Omega background weight
    (cmp99UbarPhysicalNoWindingBudget d M Nc epsilon noWinding) (by
      intro b x hx
      simpa only [cmp99UbarPhysicalNoWindingBudget_delta] using
        norm_UbarDeviationLogArg_le_physicalNoWindingBudget
          background (cmp99SourceBaseCoarseBackground background)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)
          epsilon epsilon_nonneg noWinding
          (fun e _ => fine_small e) (coarse_small b)
          (cmp99SourceUbarGamma1_length_le (G := SUN Nc) b x hx)
          (cmp99SourceUbarGamma2_length_le (G := SUN Nc) hd hM b x)
          (cmp99SourceUbarGamma3_length_le (G := SUN Nc) b x hx))

/-- A canonical scale producer requiring only fine-link smallness.  The
derived coarse transport and the sharp source no-winding radius are both
generated internally. -/
noncomputable def cmp99SourceRegionalScaleDataOfFineSmall
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (weight epsilonFine : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    CMP99PhysicalRegionalScaleData Omega background :=
  cmp99SourceRegionalScaleDataOfDeviationBudget hd hM Omega background weight
    (cmp99SourceUbarFineNoWindingBudget epsilonFine noWinding) (by
      intro b x hx
      simpa only [cmp99SourceUbarFineNoWindingBudget_delta] using
        norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
          hd hM background epsilonFine epsilonFine_nonneg fine_small b x hx)

/-- A complete source scale packages block saturation with the canonical
physical data, so the tower step consumes one coherent object. -/
structure CMP99SourceRegionalScale
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc)) where
  private mk ::
  blockSaturated : Omega.BlockSaturated
  data : CMP99PhysicalRegionalScaleData Omega background

/-- The sealed source wrapper built from the canonical contour producer. -/
noncomputable def CMP99SourceRegionalScale.ofCertificates
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (blockSaturated : Omega.BlockSaturated)
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
    CMP99SourceRegionalScale Omega background where
  blockSaturated := blockSaturated
  data := cmp99SourceRegionalScaleData hd hM Omega background weight epsilon
    epsilon_nonneg noWinding fine_small coarse_small

/-- The strongest sealed constructor currently available: the only
small-field premise is linkwise smallness of the fine background. -/
noncomputable def CMP99SourceRegionalScale.ofFineSmall
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (blockSaturated : Omega.BlockSaturated)
    (weight epsilonFine : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    CMP99SourceRegionalScale Omega background where
  blockSaturated := blockSaturated
  data := cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
    weight epsilonFine epsilonFine_nonneg noWinding fine_small

/-- Source-normalized scale: the one-step weight is no longer a caller input,
but the literal coefficient `M^{-d}` of CMP99 (3.19). -/
structure CMP99SourceNormalizedRegionalScale
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc)) where
  private mk ::
  toSourceScale : CMP99SourceRegionalScale Omega background
  weight_eq_source : toSourceScale.data.weight =
    cmp99SourceBlockAverageWeight M d

/-- Strongest normalized constructor: region saturation and fine-link
smallness produce the complete scale, including the printed averaging
coefficient. -/
noncomputable def CMP99SourceNormalizedRegionalScale.ofFineSmall
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (blockSaturated : Omega.BlockSaturated)
    (epsilonFine : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    CMP99SourceNormalizedRegionalScale Omega background where
  toSourceScale := CMP99SourceRegionalScale.ofFineSmall hd hM Omega background
    blockSaturated (cmp99SourceBlockAverageWeight M d) epsilonFine
    epsilonFine_nonneg noWinding fine_small
  weight_eq_source := rfl

/-- Build a normalized source scale directly from a physical fine region.

No block-saturation certificate is requested: the operator domain is the
canonical union of complete order-`M` blocks contained in `physicalOmega`.
This is the source-faithful interface for domains whose boundaries are fixed
by the physical distances on CMP99 printed p. 408. -/
noncomputable def CMP99SourceNormalizedRegionalScale.ofPhysicalFineRegion
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (physicalOmega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (epsilonFine : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    CMP99SourceNormalizedRegionalScale
      (cmp99BlockInteriorActiveRegion (M := M) (N' := N') physicalOmega)
      background :=
  CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM
    (cmp99BlockInteriorActiveRegion (M := M) (N' := N') physicalOmega)
    background
    (cmp99BlockInteriorActiveRegion_blockSaturated
      (M := M) (N' := N') physicalOmega)
    epsilonFine epsilonFine_nonneg noWinding fine_small

omit [NeZero Nc] in
@[simp] theorem CMP99SourceNormalizedRegionalScale.weight
    {Omega : ActiveGaugeRegion d (M * N')}
    {background : GaugeConfig d (M * N') (SUN Nc)}
    (S : CMP99SourceNormalizedRegionalScale Omega background) :
    S.toSourceScale.data.weight = cmp99SourceBlockAverageWeight M d :=
  S.weight_eq_source

omit [NeZero Nc] in
theorem CMP99SourceNormalizedRegionalScale.blockSaturated
    {Omega : ActiveGaugeRegion d (M * N')}
    {background : GaugeConfig d (M * N') (SUN Nc)}
    (S : CMP99SourceNormalizedRegionalScale Omega background) :
    Omega.BlockSaturated :=
  S.toSourceScale.blockSaturated

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
