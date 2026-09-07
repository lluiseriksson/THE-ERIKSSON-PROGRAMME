/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCSourceCutTower
import YangMills.RG.BalabanCMP95PeriodicSquarePartition

/-!
# The source-generated Section C tower in the kernel form of (3.108)

CMP99 (3.97) is rectangular: every consecutive factor acts between two
different regional carriers.  Consequently its direct contribution to the
kernel estimate (3.108) must also be stated between the genuine initial and
terminal carriers, rather than coerced to an endomorphism on an ambient
space.

This file consumes the fixed-rate weighted-row theorem for the complete
source-generated tower.  The conclusion is the pointwise kernel estimate with
amplitude `A^(j+1)` and one unchanged decay rate.  The cutoff functions are
still generated from the literal source characteristic and one global square
partition; no transition-specific cut data occurs in the statement.

Honest scope: this is the (3.108)-shaped estimate for the complete factor
tower constructed from (3.97).  It does not assert that CMP99's non-exhaustive
"etc." list has already been reconstructed or summed.
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

/-- Pointwise fixed-rate kernel estimate for the complete, rectangular,
source-generated Section C tower.  This is the directly typed contribution
of the factors (3.97) to the estimate shaped as CMP99 (3.108). -/
theorem generatedSectionCSourceCutFactorTower_exponentialKernelBound_toward_eq3108
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
    FinitePiLpTypedExponentialKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc) walk)
      (D.generatedSectionCCoarseCrossDist hpi5
        (cmp99OmegaZeroIndex j) (cmp99OmegaLastIndex j))
      ((cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
        M depth spacing epsilon rate) ^ (j + 1)) rate := by
  dsimp only
  exact finitePiLpTypedExponentialKernelBound_of_weightedRow
    _ _ hrate
    (D.generatedSectionCSourceCutFactorTower_weightedRowKernelBound P hpi5 hM
      depth hspacing hrate background budget fineSmall hsmall)

/-- CMP95-profile specialization of the rectangular contribution to (3.108).
The global square partition is generated from (1.118), rather than supplied
as a separate hypothesis. -/
theorem
    generatedCMP95SectionCSourceCutFactorTower_exponentialKernelBound_toward_eq3108
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP95SourceSmoothPartitionProfile)
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
    let squarePartition := cmp95SourcePeriodicCoarseSquarePartition P Q
    let walk := D.generatedSectionCSourceCutFactorTower squarePartition hpi5
      hM depth hspacing background budget fineSmall hsmall
    FinitePiLpTypedExponentialKernelBound
      (dependentFinitePiLpWalkOperator
        (D.GeneratedSectionCCoarseSiteFamily hpi5) (SUNLieCoord Nc) walk)
      (D.generatedSectionCCoarseCrossDist hpi5
        (cmp99OmegaZeroIndex j) (cmp99OmegaLastIndex j))
      ((cmp99SourceGeneratedPhysicalCoarseRightFactorWeightedRowAmplitude
        M depth spacing epsilon rate) ^ (j + 1)) rate := by
  dsimp only
  exact D.generatedSectionCSourceCutFactorTower_exponentialKernelBound_toward_eq3108
    (cmp95SourcePeriodicCoarseSquarePartition P Q) hpi5 hM depth hspacing
      hrate background budget fineSmall hsmall

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
