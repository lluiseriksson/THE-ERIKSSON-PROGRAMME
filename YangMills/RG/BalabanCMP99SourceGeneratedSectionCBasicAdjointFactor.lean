/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCBasicFactor

/-!
# The mixed-scale basic Section C factor

CMP99 printed p. 413 states explicitly that Section C factors generally act
between different scales and gives

`K(h'_Pi) G'_Pi h'_Pi Q'^*`

as its example: it maps the coarse `B` field to the fine `eta` lattice.  This
file realizes that exact rectangular arrow from the generated weighted
adjoint and the literal basic factor of (3.88).  Its domain remains the actual
terminal Hilbert bundle of `Q'`; the existing terminal-space equality, rather
than an identification of the coarse and fine carriers, relates it to the
original coarse site coordinates.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Direct volume-independent budget for
`K(h') G' h' Q'^*`. -/
noncomputable def cmp99SourceGeneratedPhysicalBasicAdjointFactorNormBound
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalFineBasicFactorNormBound
      M depth spacing epsilon *
    cmp99SourceGeneratedWeightedAdjointNormBound M depth

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 4000000

/-- The literal mixed-scale arrow `K(h') G' h' Q'^*`.  Its source is the
generated coarse terminal space and its target is the fine regional field. -/
noncomputable def generatedPhysicalSectionCBasicAdjointFactor
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Basic := D.generatedPhysicalFineSectionCBasicFactor P hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  exact Basic.comp T.weightedAdjoint

/-- The norm is the product of the already proved basic-factor and physical
weighted-adjoint budgets. -/
theorem norm_generatedPhysicalSectionCBasicAdjointFactor_le
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖D.generatedPhysicalSectionCBasicAdjointFactor P hpi5 s hM depth
      hspacing background budget fineSmall hsmall‖ ≤
      cmp99SourceGeneratedPhysicalBasicAdjointFactorNormBound
        M depth spacing epsilon := by
  let Omega := D.operatorCoarseRegion hpi5 s
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Basic := D.generatedPhysicalFineSectionCBasicFactor P hpi5 s hM depth
    hspacing background budget fineSmall hsmall
  let A := cmp99SourceGeneratedPhysicalFineBasicFactorNormBound
    M depth spacing epsilon
  let W := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  have hBasic : ‖Basic‖ ≤ A :=
    D.norm_generatedPhysicalFineSectionCBasicFactor_le P hpi5 s hM depth
      hspacing background budget fineSmall hsmall
  have hW : ‖T.weightedAdjoint‖ ≤ W :=
    D.norm_generatedWeightedAdjoint_le hpi5 s hM depth hspacing background
      budget fineSmall
  have hA : 0 ≤ A := (norm_nonneg Basic).trans hBasic
  unfold generatedPhysicalSectionCBasicAdjointFactor
  change ‖Basic.comp T.weightedAdjoint‖ ≤ _
  calc
    ‖Basic.comp T.weightedAdjoint‖ ≤ ‖Basic‖ * ‖T.weightedAdjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ A * W :=
      mul_le_mul hBasic hW (norm_nonneg T.weightedAdjoint) hA
    _ = cmp99SourceGeneratedPhysicalBasicAdjointFactorNormBound
        M depth spacing epsilon := rfl

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
