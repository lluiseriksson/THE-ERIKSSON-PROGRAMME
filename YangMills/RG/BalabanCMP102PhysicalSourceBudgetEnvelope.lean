/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundBallSourceNorm
import YangMills.RG.BalabanCMP98Eq123LogBound

/-!
# Scalar envelopes for the CMP102 physical chart budgets

All source budgets entering the CMP102 chart depend on a field only through
its finite source sup norm.  This module replaces that norm by one common
scalar upper bound.  It is the monotonicity bridge needed to construct every
chart on a Banach ball from a single finite list of scalar inequalities.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Scalar envelope for the complete four-contour displacement. -/
def cmp102PhysicalContourDisplacementEnvelope
    (d M : ℕ) (R t : ℝ) : ℝ :=
  (2 * (d + 1) * M : ℕ) * (2 * (|t| * R)) *
    (1 + 2 * (|t| * R)) ^ (2 * (d + 1) * M)

/-- Scalar envelope for the straight coarse-contour displacement. -/
def cmp102PhysicalCoarseContourDisplacementEnvelope
    (M : ℕ) (R t : ℝ) : ℝ :=
  (M : ℝ) * (2 * (|t| * R)) *
    (1 + 2 * (|t| * R)) ^ M

/-- Scalar envelope for the logarithmic block-average displacement. -/
def cmp102PhysicalLogAverageDisplacementEnvelope
    (d M : ℕ) (R t r : ℝ) : ℝ :=
  nearLogDerivativeBudget r *
    cmp102PhysicalContourDisplacementEnvelope d M R t

/-- Scalar envelope for the outer exponential displacement. -/
def cmp102PhysicalOuterExpDisplacementEnvelope
    (d M : ℕ) (R t r : ℝ) : ℝ :=
  let Rlog := cmp98SourceLogAverageRadius r
  let D := cmp102PhysicalLogAverageDisplacementEnvelope d M R t r
  expSecondDerivativeBudget Rlog * D ^ 2 +
    expDerivativeBudget Rlog * D

/-- Scalar envelope for the normalized physical block displacement. -/
def cmp102PhysicalBlockDisplacementEnvelope
    (d M : ℕ) (R t r : ℝ) : ℝ :=
  (cmp102PhysicalOuterExpDisplacementEnvelope d M R t r +
      cmp98SourceOuterExpNormBudget r *
        cmp102PhysicalCoarseContourDisplacementEnvelope M R t) *
    cmp98SourceOuterExpNormBudget r

/-- Replacing the source norm by a larger nonnegative scalar enlarges the
four-contour budget. -/
theorem cmp98SourceContourDisplacementBudget_le_envelope
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R t : ℝ) (hA : cmp98SourceFieldSupNorm A ≤ R) :
    cmp98SourceContourDisplacementBudget A t ≤
      cmp102PhysicalContourDisplacementEnvelope d M R t := by
  unfold cmp98SourceContourDisplacementBudget
    cmp102PhysicalContourDisplacementEnvelope
  have hq :
      |t| * cmp98SourceFieldSupNorm A ≤ |t| * R :=
    mul_le_mul_of_nonneg_left hA (abs_nonneg t)
  have hq0 : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  have hR0 : 0 ≤ R :=
    (cmp98SourceFieldSupNorm_nonneg A).trans hA
  have hqR0 : 0 ≤ |t| * R := mul_nonneg (abs_nonneg t) hR0
  gcongr

/-- The same scalar replacement enlarges the straight coarse-contour
budget. -/
theorem cmp98SourceCoarseContourDisplacementBudget_le_envelope
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R t : ℝ) (hA : cmp98SourceFieldSupNorm A ≤ R) :
    cmp98SourceCoarseContourDisplacementBudget A t ≤
      cmp102PhysicalCoarseContourDisplacementEnvelope M R t := by
  unfold cmp98SourceCoarseContourDisplacementBudget
    cmp102PhysicalCoarseContourDisplacementEnvelope
  have hq :
      |t| * cmp98SourceFieldSupNorm A ≤ |t| * R :=
    mul_le_mul_of_nonneg_left hA (abs_nonneg t)
  have hq0 : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  have hR0 : 0 ≤ R :=
    (cmp98SourceFieldSupNorm_nonneg A).trans hA
  have hqR0 : 0 ≤ |t| * R := mul_nonneg (abs_nonneg t) hR0
  gcongr

/-- The complete normalized block budget is monotone in the source-norm
envelope. -/
theorem cmp98SourcePhysicalBlockDisplacementBudget_le_envelope
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R t r : ℝ) (hr : 0 ≤ r)
    (hA : cmp98SourceFieldSupNorm A ≤ R) :
    cmp98SourcePhysicalBlockDisplacementBudget A t r ≤
      cmp102PhysicalBlockDisplacementEnvelope d M R t r := by
  have hcont :=
    cmp98SourceContourDisplacementBudget_le_envelope A R t hA
  have hcoarse :=
    cmp98SourceCoarseContourDisplacementBudget_le_envelope A R t hA
  have hnear := nearLogDerivativeBudget_nonneg r hr
  have hlog :
      cmp98SourceLogAverageDisplacementBudget A t r ≤
        cmp102PhysicalLogAverageDisplacementEnvelope d M R t r := by
    unfold cmp98SourceLogAverageDisplacementBudget
      cmp102PhysicalLogAverageDisplacementEnvelope
    exact mul_le_mul_of_nonneg_left hcont hnear
  have hlog0 :=
    cmp98SourceLogAverageDisplacementBudget_nonneg A t r hr
  have henvLog0 :
      0 ≤ cmp102PhysicalLogAverageDisplacementEnvelope d M R t r :=
    hlog0.trans hlog
  have hRlog0 := cmp98SourceLogAverageRadius_nonneg r hr
  have hsecond :=
    expSecondDerivativeBudget_nonneg
      (cmp98SourceLogAverageRadius r) hRlog0
  have hfirst :=
    expDerivativeBudget_nonneg
      (cmp98SourceLogAverageRadius r) hRlog0
  have houter :
      cmp98SourceOuterExpDisplacementBudget A t r ≤
        cmp102PhysicalOuterExpDisplacementEnvelope d M R t r := by
    unfold cmp98SourceOuterExpDisplacementBudget
      cmp102PhysicalOuterExpDisplacementEnvelope
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlog0 hlog 2) hsecond
    · exact mul_le_mul_of_nonneg_left hlog hfirst
  have hnorm : 0 ≤ cmp98SourceOuterExpNormBudget r := by
    unfold cmp98SourceOuterExpNormBudget
    positivity
  unfold cmp98SourcePhysicalBlockDisplacementBudget
    cmp102PhysicalBlockDisplacementEnvelope
  gcongr

end

end YangMills.RG
