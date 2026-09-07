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

/-- Scalar envelope for the complete four-contour quadratic remainder. -/
def cmp102PhysicalContourQuadraticEnvelope
    (d M : ℕ) (R t : ℝ) : ℝ :=
  let sourceLength : ℕ := 2 * (d + 1) * M
  (sourceLength : ℝ) ^ 2 * (2 * (|t| * R)) ^ 2 *
      (1 + 2 * (|t| * R)) ^ sourceLength +
    sourceLength * (2 * (|t| * R) ^ 2)

/-- Scalar envelope for the straight coarse-contour quadratic remainder. -/
def cmp102PhysicalCoarseContourQuadraticEnvelope
    (M : ℕ) (R t : ℝ) : ℝ :=
  (M : ℝ) ^ 2 * (2 * (|t| * R)) ^ 2 *
      (1 + 2 * (|t| * R)) ^ M +
    (M : ℝ) * (2 * (|t| * R) ^ 2)

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

/-- Scalar envelope for the complete unit-endpoint CMP102 correction. -/
def cmp102PhysicalCorrectionSourceEnvelope
    (d M : ℕ) (R r : ℝ) : ℝ :=
  let Rlog := cmp98SourceLogAverageRadius r
  let D := nearLogDerivativeBudget r *
    cmp102PhysicalContourDisplacementEnvelope d M R 1
  let Q := nearLogSecondDerivativeBudget r *
        cmp102PhysicalContourDisplacementEnvelope d M R 1 ^ 2 +
      nearLogDerivativeBudget r *
        cmp102PhysicalContourQuadraticEnvelope d M R 1
  let QE := expSecondDerivativeBudget Rlog * D ^ 2 +
    expDerivativeBudget Rlog * Q
  let B := cmp102PhysicalBlockDisplacementEnvelope d M R 1 r
  B ^ 2 / (1 - B) +
    (QE + cmp98SourceOuterExpNormBudget r *
        cmp102PhysicalCoarseContourQuadraticEnvelope M R 1 +
      cmp102PhysicalOuterExpDisplacementEnvelope d M R 1 r *
        cmp102PhysicalCoarseContourDisplacementEnvelope M R 1) *
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

/-- The four-contour quadratic budget is monotone in the source-norm
envelope. -/
theorem cmp98SourceContourQuadraticBudget_le_envelope
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R t : ℝ) (hA : cmp98SourceFieldSupNorm A ≤ R) :
    cmp98SourceContourQuadraticBudget A t ≤
      cmp102PhysicalContourQuadraticEnvelope d M R t := by
  unfold cmp98SourceContourQuadraticBudget
    cmp102PhysicalContourQuadraticEnvelope
  have hq :
      |t| * cmp98SourceFieldSupNorm A ≤ |t| * R :=
    mul_le_mul_of_nonneg_left hA (abs_nonneg t)
  have hq0 : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  have hR0 : 0 ≤ R :=
    (cmp98SourceFieldSupNorm_nonneg A).trans hA
  have hqR0 : 0 ≤ |t| * R := mul_nonneg (abs_nonneg t) hR0
  have htwo :
      2 * (|t| * cmp98SourceFieldSupNorm A) ≤ 2 * (|t| * R) :=
    mul_le_mul_of_nonneg_left hq (by norm_num)
  have htwo0 : 0 ≤ 2 * (|t| * cmp98SourceFieldSupNorm A) := by positivity
  have hbase :
      1 + 2 * (|t| * cmp98SourceFieldSupNorm A) ≤
        1 + 2 * (|t| * R) := add_le_add (le_refl 1) htwo
  apply add_le_add
  · have hprod :
        (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
              (2 * (d + 1) * M) ≤
          (2 * (|t| * R)) ^ 2 *
            (1 + 2 * (|t| * R)) ^ (2 * (d + 1) * M) :=
      mul_le_mul
        (pow_le_pow_left₀ htwo0 htwo 2)
        (pow_le_pow_left₀ (by positivity) hbase _)
        (by positivity) (by positivity)
    calc
      (2 * (d + 1) * M : ℕ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
              (2 * (d + 1) * M)
          = ((2 * (d + 1) * M : ℕ) : ℝ) ^ 2 *
              ((2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
                (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
                  (2 * (d + 1) * M)) := by norm_num; ring
      _ ≤ ((2 * (d + 1) * M : ℕ) : ℝ) ^ 2 *
              ((2 * (|t| * R)) ^ 2 *
                (1 + 2 * (|t| * R)) ^ (2 * (d + 1) * M)) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
      _ = (2 * (d + 1) * M : ℕ) ^ 2 *
            (2 * (|t| * R)) ^ 2 *
            (1 + 2 * (|t| * R)) ^ (2 * (d + 1) * M) := by
              norm_num
              ring
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hq0 hq 2) (by norm_num)

/-- The coarse-contour quadratic budget is monotone in the source-norm
envelope. -/
theorem cmp98SourceCoarseContourQuadraticBudget_le_envelope
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R t : ℝ) (hA : cmp98SourceFieldSupNorm A ≤ R) :
    cmp98SourceCoarseContourQuadraticBudget A t ≤
      cmp102PhysicalCoarseContourQuadraticEnvelope M R t := by
  unfold cmp98SourceCoarseContourQuadraticBudget
    cmp102PhysicalCoarseContourQuadraticEnvelope
  have hq :
      |t| * cmp98SourceFieldSupNorm A ≤ |t| * R :=
    mul_le_mul_of_nonneg_left hA (abs_nonneg t)
  have hq0 : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  have hR0 : 0 ≤ R :=
    (cmp98SourceFieldSupNorm_nonneg A).trans hA
  have hqR0 : 0 ≤ |t| * R := mul_nonneg (abs_nonneg t) hR0
  have htwo :
      2 * (|t| * cmp98SourceFieldSupNorm A) ≤ 2 * (|t| * R) :=
    mul_le_mul_of_nonneg_left hq (by norm_num)
  have htwo0 : 0 ≤ 2 * (|t| * cmp98SourceFieldSupNorm A) := by positivity
  have hbase :
      1 + 2 * (|t| * cmp98SourceFieldSupNorm A) ≤
        1 + 2 * (|t| * R) := add_le_add (le_refl 1) htwo
  apply add_le_add
  · have hprod :
        (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ M ≤
          (2 * (|t| * R)) ^ 2 *
            (1 + 2 * (|t| * R)) ^ M :=
      mul_le_mul
        (pow_le_pow_left₀ htwo0 htwo 2)
        (pow_le_pow_left₀ (by positivity) hbase _)
        (by positivity) (by positivity)
    calc
      (M : ℝ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ M
          = (M : ℝ) ^ 2 *
              ((2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
                (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ M) := by ring
      _ ≤ (M : ℝ) ^ 2 *
              ((2 * (|t| * R)) ^ 2 *
                (1 + 2 * (|t| * R)) ^ M) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
      _ = (M : ℝ) ^ 2 * (2 * (|t| * R)) ^ 2 *
            (1 + 2 * (|t| * R)) ^ M := by ring
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hq0 hq 2) (by norm_num)

/-- The outer exponential displacement is monotone in the source-norm
envelope. -/
theorem cmp98SourceOuterExpDisplacementBudget_le_envelope
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R t r : ℝ) (hr : 0 ≤ r)
    (hA : cmp98SourceFieldSupNorm A ≤ R) :
    cmp98SourceOuterExpDisplacementBudget A t r ≤
      cmp102PhysicalOuterExpDisplacementEnvelope d M R t r := by
  have hcont :=
    cmp98SourceContourDisplacementBudget_le_envelope A R t hA
  have hnear := nearLogDerivativeBudget_nonneg r hr
  have hlog :
      cmp98SourceLogAverageDisplacementBudget A t r ≤
        cmp102PhysicalLogAverageDisplacementEnvelope d M R t r := by
    unfold cmp98SourceLogAverageDisplacementBudget
      cmp102PhysicalLogAverageDisplacementEnvelope
    exact mul_le_mul_of_nonneg_left hcont hnear
  have hlog0 :=
    cmp98SourceLogAverageDisplacementBudget_nonneg A t r hr
  have hRlog0 := cmp98SourceLogAverageRadius_nonneg r hr
  have hsecond :=
    expSecondDerivativeBudget_nonneg
      (cmp98SourceLogAverageRadius r) hRlog0
  have hfirst :=
    expDerivativeBudget_nonneg
      (cmp98SourceLogAverageRadius r) hRlog0
  unfold cmp98SourceOuterExpDisplacementBudget
    cmp102PhysicalOuterExpDisplacementEnvelope
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlog0 hlog 2) hsecond
  · exact mul_le_mul_of_nonneg_left hlog hfirst

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
    exact cmp98SourceOuterExpDisplacementBudget_le_envelope
      A R t r hr hA
  have hnorm : 0 ≤ cmp98SourceOuterExpNormBudget r := by
    unfold cmp98SourceOuterExpNormBudget
    positivity
  unfold cmp98SourcePhysicalBlockDisplacementBudget
    cmp102PhysicalBlockDisplacementEnvelope
  gcongr

set_option maxHeartbeats 3000000 in
/-- The explicit CMP102 correction source budget is monotone in the common
source-norm envelope, provided the envelope remains inside the logarithmic
denominator. -/
theorem cmp102PhysicalCorrectionSourceBudget_le_envelope
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (R r : ℝ) (hr : 0 ≤ r)
    (hA : cmp98SourceFieldSupNorm A ≤ R)
    (hBlt : cmp102PhysicalBlockDisplacementEnvelope d M R 1 r < 1) :
    cmp102PhysicalCorrectionSourceBudget A r ≤
      cmp102PhysicalCorrectionSourceEnvelope d M R r := by
  let BA := cmp98SourcePhysicalBlockDisplacementBudget A 1 r
  let BE := cmp102PhysicalBlockDisplacementEnvelope d M R 1 r
  have hB : BA ≤ BE :=
    cmp98SourcePhysicalBlockDisplacementBudget_le_envelope
      A R 1 r hr hA
  have hBA0 : 0 ≤ BA := by
    dsimp only [BA]
    unfold cmp98SourcePhysicalBlockDisplacementBudget
    have hRlog0 := cmp98SourceLogAverageRadius_nonneg r hr
    have houter0 : 0 ≤ cmp98SourceOuterExpDisplacementBudget A 1 r := by
      unfold cmp98SourceOuterExpDisplacementBudget
      have hlog0 :=
        cmp98SourceLogAverageDisplacementBudget_nonneg A 1 r hr
      have hsecond :=
        expSecondDerivativeBudget_nonneg
          (cmp98SourceLogAverageRadius r) hRlog0
      have hfirst :=
        expDerivativeBudget_nonneg
          (cmp98SourceLogAverageRadius r) hRlog0
      positivity
    have hnorm0 : 0 ≤ cmp98SourceOuterExpNormBudget r := by
      unfold cmp98SourceOuterExpNormBudget
      have hsecond :=
        expSecondDerivativeBudget_nonneg
          (cmp98SourceLogAverageRadius r) hRlog0
      have hfirst :=
        expDerivativeBudget_nonneg
          (cmp98SourceLogAverageRadius r) hRlog0
      positivity
    have hcoarse0 :=
      cmp98SourceCoarseContourDisplacementBudget_nonneg A 1
    positivity
  have hBE0 : 0 ≤ BE := hBA0.trans hB
  have hdenA : 0 < 1 - BA := sub_pos.mpr (hB.trans_lt hBlt)
  have hdenE : 0 < 1 - BE := sub_pos.mpr hBlt
  have hratio :
      BA ^ 2 / (1 - BA) ≤ BE ^ 2 / (1 - BE) := by
    exact div_le_div₀
      (sq_nonneg BE)
      (pow_le_pow_left₀ hBA0 hB 2)
      hdenE
      (by linarith)
  have hcont :=
    cmp98SourceContourDisplacementBudget_le_envelope A R 1 hA
  have hcontQ :=
    cmp98SourceContourQuadraticBudget_le_envelope A R 1 hA
  have hcoarse :=
    cmp98SourceCoarseContourDisplacementBudget_le_envelope A R 1 hA
  have hcoarseQ :=
    cmp98SourceCoarseContourQuadraticBudget_le_envelope A R 1 hA
  have houter :=
    cmp98SourceOuterExpDisplacementBudget_le_envelope A R 1 r hr hA
  have houter0 : 0 ≤ cmp98SourceOuterExpDisplacementBudget A 1 r := by
    unfold cmp98SourceOuterExpDisplacementBudget
    have hlog0 :=
      cmp98SourceLogAverageDisplacementBudget_nonneg A 1 r hr
    have hRlog0' := cmp98SourceLogAverageRadius_nonneg r hr
    have hsecond' :=
      expSecondDerivativeBudget_nonneg
        (cmp98SourceLogAverageRadius r) hRlog0'
    have hfirst' :=
      expDerivativeBudget_nonneg
        (cmp98SourceLogAverageRadius r) hRlog0'
    positivity
  have henvOuter0 :
      0 ≤ cmp102PhysicalOuterExpDisplacementEnvelope d M R 1 r :=
    houter0.trans houter
  have hRlog0 := cmp98SourceLogAverageRadius_nonneg r hr
  have hnear1 := nearLogDerivativeBudget_nonneg r hr
  have hnear2 := nearLogSecondDerivativeBudget_nonneg r hr
  have hexp1 :=
    expDerivativeBudget_nonneg (cmp98SourceLogAverageRadius r) hRlog0
  have hexp2 :=
    expSecondDerivativeBudget_nonneg
      (cmp98SourceLogAverageRadius r) hRlog0
  have hnorm : 0 ≤ cmp98SourceOuterExpNormBudget r := by
    unfold cmp98SourceOuterExpNormBudget
    positivity
  unfold cmp102PhysicalCorrectionSourceBudget
    cmp102PhysicalCorrectionSourceEnvelope
  dsimp only
  apply add_le_add hratio
  apply mul_le_mul_of_nonneg_right _ hnorm
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀
            (mul_nonneg hnear1
              (cmp98SourceContourDisplacementBudget_nonneg A 1))
            (mul_le_mul_of_nonneg_left hcont hnear1) 2)
          hexp2
      · apply mul_le_mul_of_nonneg_left _ hexp1
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀
              (cmp98SourceContourDisplacementBudget_nonneg A 1)
              hcont 2) hnear2
        · exact mul_le_mul_of_nonneg_left hcontQ hnear1
    · exact mul_le_mul_of_nonneg_left hcoarseQ hnorm
  · exact mul_le_mul houter hcoarse
      (cmp98SourceCoarseContourDisplacementBudget_nonneg A 1)
      henvOuter0

end

end YangMills.RG
