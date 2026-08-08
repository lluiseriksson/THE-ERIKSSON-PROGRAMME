/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395PhysicalFamily
import YangMills.RG.BalabanCMP99PatchedParametrixNeumann

/-!
# The physical Neumann correction of CMP99 equation (3.95)

The source-family theorem has the exact orientation

`A * C0 = 1 - R`.

Consequently the corrected covariance is `C0 * sum_n R^n`.  This file
constructs that operator from the generated physical objects of (3.95) and
proves that it is an exact right inverse of the generated global middle.

The contraction `norm R < 1` remains visible.  It is the genuine analytic
obligation that must later be discharged by the complete Section C walk
expansion; it is not replaced here by a bound on a non-exhaustive displayed
subalphabet.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- The literal smooth regional sum `C0 = sum_Pi h_Pi C_Pi h_Pi` in (3.95). -/
noncomputable def cmp99Eq395PhysicalPatchedCovariance
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) : CMP99Eq395AmbientOperator Q Nc :=
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall
  ∑ cell : FinBox 4 Q, h cell * C cell * h cell

/-- The literal physical correction `R` produced by the source family in
CMP99 (3.95). -/
noncomputable def cmp99Eq395PhysicalCorrection
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) : CMP99Eq395AmbientOperator Q Nc :=
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P
  let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc)
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall
  cmp99Eq395R Finset.univ A AD chi h C

/-- The exact physical Neumann candidate
`C0 * sum_n R^n = C0 * (1 - R)^(-1)` generated from (3.95). -/
noncomputable def cmp99Eq395PhysicalCorrectedCovariance
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) : CMP99Eq395AmbientOperator Q Nc :=
  cmp99CorrectedParametrix
    (cmp99Eq395PhysicalPatchedCovariance D hpi5 P hM depth hspacing
      background budget fineSmall hsmall)
    (-cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing background
      budget fineSmall hsmall)

/-- The corrected physical covariance is visibly the regional parametrix
followed by the geometric series in the literal correction `R`. -/
theorem cmp99Eq395PhysicalCorrectedCovariance_eq_tsum_pow
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth hspacing
        background budget fineSmall hsmall =
      (cmp99Eq395PhysicalPatchedCovariance D hpi5 P hM depth hspacing
        background budget fineSmall hsmall).comp
        (∑' n : ℕ, (cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing
          background budget fineSmall hsmall) ^ n) := by
  rw [cmp99Eq395PhysicalCorrectedCovariance, cmp99CorrectedParametrix,
    cmp99PatchedDefectNeumannInverse_neg_eq_tsum_pow]

/-- The generated global middle composed with the corrected physical
covariance is the identity.  The sole extra hypothesis is contraction of the
literal correction `R` from (3.95). -/
theorem cmp99Eq395PhysicalGlobalMiddle_comp_correctedCovariance_eq_id
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (hR : ‖cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing
      background budget fineSmall hsmall‖ < 1) :
    (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
      fineSmall hsmall).comp
        (cmp99Eq395PhysicalCorrectedCovariance D hpi5 P hM depth hspacing
          background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ
        (GaugeZeroCochain 4 (2 * Q) (SUNLieCoord Nc)) := by
  rw [cmp99Eq395PhysicalCorrectedCovariance]
  apply comp_cmp99CorrectedParametrix_eq_id
  · change
      cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
          fineSmall hsmall *
          cmp99Eq395PhysicalPatchedCovariance D hpi5 P hM depth hspacing
            background budget fineSmall hsmall =
        1 + -cmp99Eq395PhysicalCorrection D hpi5 P hM depth hspacing
          background budget fineSmall hsmall
    simpa [cmp99Eq395PhysicalPatchedCovariance,
      cmp99Eq395PhysicalCorrection, sub_eq_add_neg] using
      (cmp99Eq395_physical_global_middle_source_family D hpi5 P hM depth
        hspacing background budget fineSmall hsmall)
  · rw [norm_neg]
    exact hR

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
