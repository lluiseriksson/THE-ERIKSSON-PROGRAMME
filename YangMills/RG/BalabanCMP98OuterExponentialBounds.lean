/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98SourceNearLogDomain

/-!
# Source-explicit displacement and background norm of the CMP98 outer exponential

The quadratic outer-exponential estimate is already available in source
coordinates.  This file adds the two companion bounds required by the exact
two-factor identity: displacement of the exponential curve and the norm of
its value (and inverse value) at the background.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98OuterExponentialBoundsMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Displacement budget of the logarithmic block average. -/
def cmp98SourceLogAverageDisplacementBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t r : ℝ) : ℝ :=
  nearLogDerivativeBudget r * cmp98SourceContourDisplacementBudget A t

/-- Displacement budget of the outer exponential. -/
def cmp98SourceOuterExpDisplacementBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t r : ℝ) : ℝ :=
  let R := cmp98SourceLogAverageRadius r
  let D := cmp98SourceLogAverageDisplacementBudget A t r
  expSecondDerivativeBudget R * D ^ 2 + expDerivativeBudget R * D

/-- Uniform norm budget for the background outer exponential and its
inverse exponential. -/
def cmp98SourceOuterExpNormBudget (r : ℝ) : ℝ :=
  let R := cmp98SourceLogAverageRadius r
  1 + expSecondDerivativeBudget R * R ^ 2 + expDerivativeBudget R * R

theorem cmp98SourceLogAverageDisplacementBudget_nonneg
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t r : ℝ) (hr : 0 ≤ r) :
    0 ≤ cmp98SourceLogAverageDisplacementBudget A t r := by
  unfold cmp98SourceLogAverageDisplacementBudget
  exact mul_nonneg (nearLogDerivativeBudget_nonneg r hr)
    (cmp98SourceContourDisplacementBudget_nonneg A t)

set_option maxHeartbeats 1000000 in
/-- The source logarithmic displacement gives an explicit displacement
bound for the outer noncommutative exponential. -/
theorem norm_cmp98UbarExpAverage_physicalLine_sub_zero_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    ‖cmp98UbarExpAverage U b
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) -
        cmp98UbarExpAverage U b 0‖ ≤
      cmp98SourceOuterExpDisplacementBudget A t r := by
  let R := cmp98SourceLogAverageRadius r
  let D := cmp98SourceLogAverageDisplacementBudget A t r
  let Yt := cmp98UbarLogAverage U b
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  let Y0 := cmp98UbarLogAverage U b 0
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    linarith [cmp98SourceContourDisplacementBudget_nonneg A t]
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hR0 : 0 ≤ R := cmp98SourceLogAverageRadius_nonneg r hr0
  have hYt : ‖Yt‖ ≤ R := by
    simpa [Yt, R] using
      norm_cmp98UbarLogAverage_physicalLine_le_sourceRadius
        U A b t r hbase hsmall hr hr1
  have hY0base : ‖Y0‖ ≤ nearLogDerivativeBudget r * (1 / 3 : ℝ) := by
    simpa [Y0] using norm_cmp98UbarLogAverage_zero_le U b r hbase hr13 hr1
  have hY0 : ‖Y0‖ ≤ R := by
    have hB1 := nearLogDerivativeBudget_nonneg r hr0
    exact hY0base.trans (by
      dsimp only [R, cmp98SourceLogAverageRadius]
      exact mul_le_mul_of_nonneg_left hr13 hB1)
  have hdiff : ‖Yt - Y0‖ ≤ D := by
    simpa [Yt, Y0, D, cmp98SourceLogAverageDisplacementBudget] using
      norm_cmp98UbarLogAverage_physicalLine_sub_zero_le
        U A b t r hbase hsmall hr hr1
  have hraw := norm_exp_sub_exp_le_derivativeBudgets hR0 hYt hY0
  have hB2 := expSecondDerivativeBudget_nonneg R hR0
  have hB1 := expDerivativeBudget_nonneg R hR0
  have hD0 := cmp98SourceLogAverageDisplacementBudget_nonneg A t r hr0
  have hsq : ‖Yt - Y0‖ ^ 2 ≤ D ^ 2 :=
    sq_le_sq₀ (norm_nonneg _) hD0 |>.2 hdiff
  change ‖NormedSpace.exp Yt - NormedSpace.exp Y0‖ ≤ _
  dsimp only [cmp98SourceOuterExpDisplacementBudget]
  change ‖NormedSpace.exp Yt - NormedSpace.exp Y0‖ ≤
    expSecondDerivativeBudget R * D ^ 2 + expDerivativeBudget R * D
  exact hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_left hsq hB2)
    (mul_le_mul_of_nonneg_left hdiff hB1))

/-- The background outer exponential has a source-explicit norm budget. -/
theorem norm_cmp98UbarExpAverage_zero_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hr13 : 1 / 3 ≤ r) (hr1 : r < 1) :
    ‖cmp98UbarExpAverage U b 0‖ ≤ cmp98SourceOuterExpNormBudget r := by
  let R := cmp98SourceLogAverageRadius r
  let Y0 := cmp98UbarLogAverage U b 0
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hR0 : 0 ≤ R := cmp98SourceLogAverageRadius_nonneg r hr0
  have hY0base : ‖Y0‖ ≤ nearLogDerivativeBudget r * (1 / 3 : ℝ) := by
    simpa [Y0] using norm_cmp98UbarLogAverage_zero_le U b r hbase hr13 hr1
  have hY0 : ‖Y0‖ ≤ R := by
    have hB1 := nearLogDerivativeBudget_nonneg r hr0
    exact hY0base.trans (by
      dsimp only [R, cmp98SourceLogAverageRadius]
      exact mul_le_mul_of_nonneg_left hr13 hB1)
  have hraw := norm_exp_le_derivativeBudgets hR0 hY0
  simpa [cmp98UbarExpAverage, cmp98SourceOuterExpNormBudget, R, Y0] using hraw

end

end YangMills.RG

