/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientExpAverageBudget
import YangMills.RG.BalabanCMP102AmbientNonlinearBlockGeneratedContour

/-!
# Fully source-generated budgets for the CMP102 represented block

This module combines the literal straight-contour estimates with the
generated logarithm-average-exponential estimates.  The resulting derivative
and derivative-Lipschitz budgets for the represented nonlinear block depend
only on the ambient radius, the Mercator radius, and the source dimensions.
No factor-level analytic constant remains in the public endpoint.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Fully generated derivative budget for the represented nonlinear block. -/
def cmp102SourceAmbientNonlinearBlockDerivativeBudget
    (d M : ℕ) (r q : ℝ) : ℝ :=
  cmp102AmbientNonlinearBlockDerivativeBudget
    (cmp102SourceExpAverageDerivativeBudget d M r q)
    (cmp102SourceCoarseContourValueBudget M r)
    (cmp102SourceExpAverageValueBudget q)
    (cmp102SourceCoarseContourDerivativeBudget M r)

/-- Fully generated derivative-Lipschitz budget for the represented block. -/
def cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget
    (d M : ℕ) (r q : ℝ) : ℝ :=
  cmp102AmbientNonlinearBlockDerivativeLipschitzBudget
    (cmp102SourceExpAverageDerivativeLipschitzBudget d M r q)
    (cmp102SourceCoarseContourValueBudget M r)
    (cmp102SourceExpAverageDerivativeBudget d M r q)
    (cmp102SourceCoarseContourValueLipschitzBudget M r)
    (cmp102SourceExpAverageValueLipschitzBudget d M r q)
    (cmp102SourceCoarseContourDerivativeBudget M r)
    (cmp102SourceExpAverageValueBudget q)
    (cmp102SourceCoarseContourDerivativeLipschitzBudget M r)

theorem cmp102SourceExpAverageValueBudget_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceExpAverageValueBudget q := by
  unfold cmp102SourceExpAverageValueBudget
  have hR := cmp102SourceLogAverageRadius_nonneg hq0
  have hB₂ := expSecondDerivativeBudget_nonneg _ hR
  have hB₁ := expDerivativeBudget_nonneg _ hR
  positivity

theorem cmp102SourceExpAverageDerivativeBudget_nonneg
    {d M : ℕ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceExpAverageDerivativeBudget d M r q := by
  unfold cmp102SourceExpAverageDerivativeBudget
  have hR := cmp102SourceLogAverageRadius_nonneg hq0
  have hB₁ := expDerivativeBudget_nonneg _ hR
  unfold cmp102SourceLocalNearLogDerivativeBudget
  unfold cmp102SourceFourContourDeviationDerivativeBudget
  exact mul_nonneg hB₁
    (mul_nonneg (nearLogDerivativeBudget_nonneg q hq0)
      (cmp98AmbientWilsonLineDerivativeBudget_nonneg hr _))

theorem cmp102SourceExpAverageValueLipschitzBudget_nonneg
    {d M : ℕ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceExpAverageValueLipschitzBudget d M r q := by
  unfold cmp102SourceExpAverageValueLipschitzBudget
  have hR := cmp102SourceLogAverageRadius_nonneg hq0
  unfold cmp102SourceLocalNearLogValueLipschitzBudget
  unfold cmp102SourceFourContourDeviationValueLipschitzBudget
  exact mul_nonneg (cmp102ExpLipschitzBudget_nonneg _ hR)
    (mul_nonneg (nearLogDerivativeBudget_nonneg q hq0)
      (cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr _))

theorem cmp102SourceExpAverageDerivativeLipschitzBudget_nonneg
    {d M : ℕ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceExpAverageDerivativeLipschitzBudget d M r q := by
  have hR := cmp102SourceLogAverageRadius_nonneg hq0
  have hLV :
      0 ≤ cmp102SourceLocalNearLogValueLipschitzBudget d M r q := by
    unfold cmp102SourceLocalNearLogValueLipschitzBudget
    unfold cmp102SourceFourContourDeviationValueLipschitzBudget
    exact mul_nonneg (nearLogDerivativeBudget_nonneg q hq0)
      (cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr _)
  have hLD :
      0 ≤ cmp102SourceLocalNearLogDerivativeBudget d M r q := by
    unfold cmp102SourceLocalNearLogDerivativeBudget
    unfold cmp102SourceFourContourDeviationDerivativeBudget
    exact mul_nonneg (nearLogDerivativeBudget_nonneg q hq0)
      (cmp98AmbientWilsonLineDerivativeBudget_nonneg hr _)
  have hLDL :
      0 ≤ cmp102SourceLocalNearLogDerivativeLipschitzBudget d M r q := by
    unfold cmp102SourceLocalNearLogDerivativeLipschitzBudget
    unfold cmp102SourceFourContourDeviationValueLipschitzBudget
      cmp102SourceFourContourDeviationDerivativeBudget
      cmp102SourceFourContourDeviationDerivativeLipschitzBudget
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (nearLogSecondDerivativeBudget_nonneg q hq0)
          (cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr _))
        (cmp98AmbientWilsonLineDerivativeBudget_nonneg hr _))
      (mul_nonneg (nearLogDerivativeBudget_nonneg q hq0)
        (cmp98AmbientWilsonLineDerivativeLipschitzBudget_nonneg hr _))
  unfold cmp102SourceExpAverageDerivativeLipschitzBudget
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (expSecondDerivativeBudget_nonneg _ hR) hLV) hLD)
    (mul_nonneg (expDerivativeBudget_nonneg _ hR) hLDL)

theorem cmp102SourceAmbientNonlinearBlockDerivativeBudget_nonneg
    {d M : ℕ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceAmbientNonlinearBlockDerivativeBudget d M r q := by
  unfold cmp102SourceAmbientNonlinearBlockDerivativeBudget
    cmp102AmbientNonlinearBlockDerivativeBudget
    cmp102SourceCoarseContourValueBudget
    cmp102SourceCoarseContourDerivativeBudget
  exact add_nonneg
    (mul_nonneg
      (cmp102SourceExpAverageDerivativeBudget_nonneg hr hq0)
      (cmp98AmbientWilsonLineValueBudget_nonneg hr _))
    (mul_nonneg
      (cmp102SourceExpAverageValueBudget_nonneg hq0)
      (cmp98AmbientWilsonLineDerivativeBudget_nonneg hr _))

theorem cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget_nonneg
    {d M : ℕ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget d M r q := by
  have hDDE :=
    cmp102SourceExpAverageDerivativeLipschitzBudget_nonneg
      (d := d) (M := M) hr hq0
  have hC :=
    cmp98AmbientWilsonLineValueBudget_nonneg hr M
  have hDE :=
    cmp102SourceExpAverageDerivativeBudget_nonneg
      (d := d) (M := M) hr hq0
  have hLC :=
    cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr M
  have hLE :=
    cmp102SourceExpAverageValueLipschitzBudget_nonneg
      (d := d) (M := M) hr hq0
  have hDC :=
    cmp98AmbientWilsonLineDerivativeBudget_nonneg hr M
  have hE := cmp102SourceExpAverageValueBudget_nonneg hq0
  have hDDC :=
    cmp98AmbientWilsonLineDerivativeLipschitzBudget_nonneg hr M
  unfold cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget
    cmp102AmbientNonlinearBlockDerivativeLipschitzBudget
    cmp102SourceCoarseContourValueBudget
    cmp102SourceCoarseContourDerivativeBudget
    cmp102SourceCoarseContourValueLipschitzBudget
    cmp102SourceCoarseContourDerivativeLipschitzBudget
  exact add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg hDDE hC) (mul_nonneg hDE hLC))
      (mul_nonneg hLE hDC))
    (mul_nonneg hE hDDC)

/-- The represented-block derivative is generated solely from source
contour, ambient-radius, and Mercator-radius data. -/
theorem norm_fderiv_cmp102AmbientNonlinearBlock_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q) :
    ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z‖ ≤
      cmp102SourceAmbientNonlinearBlockDerivativeBudget d M r q := by
  unfold cmp102SourceAmbientNonlinearBlockDerivativeBudget
  apply norm_fderiv_cmp102AmbientNonlinearBlock_le_of_generatedContour
    U b Z hr hZ
  · intro x hx
    exact (hD x hx).trans_lt hq1
  · exact norm_fderiv_cmp98UbarExpAverage_le_sourceBudget
      U b Z hr hq0 hq1 hZ hD
  · exact norm_cmp98UbarExpAverage_le_sourceBudget U b Z hq0 hq1 hD

/-- The represented-block derivative-Lipschitz estimate is generated solely
from the two source fields and their common radius data. -/
theorem norm_fderiv_cmp102AmbientNonlinearBlock_sub_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q)
    (hDW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ ≤ q) :
    ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) W‖ ≤
      cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget d M r q *
        ‖Z - W‖ := by
  unfold cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget
  apply norm_fderiv_cmp102AmbientNonlinearBlock_sub_le_of_generatedContour
    U b Z W hr hZ hW
  · intro x hx
    exact (hDZ x hx).trans_lt hq1
  · intro x hx
    exact (hDW x hx).trans_lt hq1
  · exact cmp102SourceExpAverageDerivativeLipschitzBudget_nonneg hr hq0
  · exact cmp102SourceExpAverageValueLipschitzBudget_nonneg hr hq0
  · exact norm_fderiv_cmp98UbarExpAverage_le_sourceBudget
      U b W hr hq0 hq1 hW hDW
  · exact norm_cmp98UbarExpAverage_le_sourceBudget U b W hq0 hq1 hDW
  · exact norm_fderiv_cmp98UbarExpAverage_sub_le_sourceBudget
      U b Z W hr hq0 hq1 hZ hW hDZ hDW
  · exact norm_cmp98UbarExpAverage_sub_le_sourceBudget
      U b Z W hr hq0 hq1 hZ hW hDZ hDW

end

end YangMills.RG
