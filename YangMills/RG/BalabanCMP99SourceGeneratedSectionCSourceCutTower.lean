/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCTypedTower
import YangMills.RG.BalabanCMP99SourcePartitionCutoffs

/-!
# Source-generated CMP99 Section C cut tower

This is the first public tower interface in which the two diagonal functions
of (3.97) are not transition inputs.  The exterior multiplier is the literal
source-cell characteristic and every `h_Pi` is obtained by restricting one
global square partition of unity.
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

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

/-- Full ordered Section C tower with all diagonal cuts generated from the
literal source characteristic and a single square partition. -/
noncomputable def generatedSectionCSourceCutFactorTower
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  D.generatedSectionCCutFactorTower hpi5
    (fun r => D.generatedSectionCSourceTransitionCutData P hpi5 r)
    hM depth hspacing background budget fineSmall hsmall

@[simp] theorem generatedSectionCSourceCutFactorTower_length
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    (D.generatedSectionCSourceCutFactorTower P hpi5 hM depth hspacing
      background budget fineSmall hsmall).length = j + 1 := by
  simp [generatedSectionCSourceCutFactorTower]

/-- The source-generated tower inherits the fixed-rate weighted-row bound;
there are no transition-specific cutoff functions or cutoff estimates in the
statement. -/
theorem generatedSectionCSourceCutFactorTower_weightedRowKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let walk := D.generatedSectionCSourceCutFactorTower P hpi5 hM depth
      hspacing background budget fineSmall hsmall
    FinitePiLpTypedWeightedRowKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc) walk)
      (D.generatedSectionCCoarseCrossDist hpi5
        (cmp99OmegaZeroIndex j) (cmp99OmegaLastIndex j))
      ((cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
        M depth spacing epsilon rate) ^ (j + 1)) rate := by
  simpa [generatedSectionCSourceCutFactorTower] using
    D.generatedSectionCCutFactorTower_weightedRowKernelBound hpi5
      (fun r => D.generatedSectionCSourceTransitionCutData P hpi5 r)
      hM depth hspacing hrate background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
