/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalRightInverseBackgroundLipschitz

/-!
# Background Lipschitz control of the CMP98 block derivative

Before right trivialization, the derivative of the literal nonlinear block is

`D exp(Y(U))[H(U)] * C(U) + exp(Y(U)) * C'(U)`.

This file compares that expression with the trivial-background expression by
four exact two-factor telescopes.  Every estimate is produced from the
source-contour bounds; the final coefficient is independent of the periodic
volume and multiplies only the genuine CMP109 tangent norm.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

set_option maxHeartbeats 2000000

local instance cmp102PhysicalBlockDerivativeBackgroundMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Literal physical first variation of the two-factor CMP98 block, before
right trivialization. -/
noncomputable def cmp98Eq119NonlinearBlockPhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98UbarExpAveragePhysicalVariation U A b *
      cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 +
    cmp98UbarExpAverage U b 0 *
      cmp98ContourFirstVariation U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0

/-- Coefficient of the source tangent norm in the block derivative at one
fixed small background. -/
def cmp102PhysicalBlockDerivativeLinearBudget
    (d M : ℕ) (r : ℝ) : ℝ :=
  let R := cmp102SourceLogAverageRadius r
  let m : ℝ := ((2 * (d + 1) * M : ℕ) : ℝ)
  expDerivativeBudget R * nearLogDerivativeBudget r * m +
    cmp98SourceOuterExpNormBudget r * (M : ℝ)

/-- Coefficient of the source tangent norm in the difference of block
derivatives between a small background and the trivial background. -/
def cmp102PhysicalBlockDerivativeBackgroundBudget
    (d M : ℕ) (r ε : ℝ) : ℝ :=
  let R := cmp102SourceLogAverageRadius r
  let m : ℝ := ((2 * (d + 1) * M : ℕ) : ℝ)
  cmp102PhysicalExpAverageBackgroundDerivativeBudget d M r ε +
    (expDerivativeBudget R * nearLogDerivativeBudget r * m) *
      ((M : ℝ) * ε) +
    cmp102PhysicalExpAverageBackgroundValueBudget d M r ε * (M : ℝ) +
    cmp98SourceOuterExpNormBudget r * ((M : ℝ) ^ 2 * ε)

theorem cmp102PhysicalBlockDerivativeLinearBudget_nonneg
    {d M : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ cmp102PhysicalBlockDerivativeLinearBudget d M r := by
  unfold cmp102PhysicalBlockDerivativeLinearBudget
  let R := cmp102SourceLogAverageRadius r
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (expDerivativeBudget_nonneg R
          (cmp102SourceLogAverageRadius_nonneg hr))
        (nearLogDerivativeBudget_nonneg r hr))
      (by positivity))
    (mul_nonneg
      (cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hr)
      (Nat.cast_nonneg M))

theorem cmp102PhysicalBlockDerivativeBackgroundBudget_nonneg
    {d M : ℕ} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    0 ≤ cmp102PhysicalBlockDerivativeBackgroundBudget d M r ε := by
  unfold cmp102PhysicalBlockDerivativeBackgroundBudget
  let R := cmp102SourceLogAverageRadius r
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · exact
          cmp102PhysicalExpAverageBackgroundDerivativeBudget_nonneg hr hε
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (expDerivativeBudget_nonneg R
                (cmp102SourceLogAverageRadius_nonneg hr))
              (nearLogDerivativeBudget_nonneg r hr))
            (by positivity))
          (mul_nonneg (Nat.cast_nonneg M) hε)
    · exact mul_nonneg
        (cmp102PhysicalExpAverageBackgroundValueBudget_nonneg hr hε)
        (Nat.cast_nonneg M)
  · exact mul_nonneg
      (cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hr)
      (mul_nonneg (sq_nonneg _) hε)

/-- The literal block derivative has a source-scale tangent bound at any
background satisfying the physical Mercator-ball hypothesis. -/
theorem norm_cmp98Eq119NonlinearBlockPhysicalVariation_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hr13 : 1 / 3 ≤ r) (hr1 : r < 1) :
    ‖cmp98Eq119NonlinearBlockPhysicalVariation U A b‖ ≤
      cmp102PhysicalBlockDerivativeLinearBudget d M r *
        cmp98SourceFieldSupNorm A := by
  let E := cmp98UbarExpAverage U b 0
  let EV := cmp98UbarExpAveragePhysicalVariation U A b
  let C := cmp98ContourMatrixCurve U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let CV := cmp98ContourFirstVariation U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let R := cmp102SourceLogAverageRadius r
  let m : ℝ := ((2 * (d + 1) * M : ℕ) : ℝ)
  let O := cmp98SourceOuterExpNormBudget r
  let S := cmp98SourceFieldSupNorm A
  have hEV : ‖EV‖ ≤
      expDerivativeBudget R * nearLogDerivativeBudget r * m * S := by
    simpa only [EV, R, m, S] using
      norm_cmp98UbarExpAveragePhysicalVariation_le_sourceScale
        U A b r hbase hr13 hr1
  have hC : ‖C‖ = 1 := by
    exact norm_cmp98ContourMatrixCurve_eq_one U A _ 0
  have hE : ‖E‖ ≤ O := by
    simpa only [E, O] using
      norm_cmp98UbarExpAverage_zero_le_sourceBudget
        U b r hbase hr13 hr1
  have hCV : ‖CV‖ ≤ (M : ℝ) * S := by
    simpa only [CV, S, cmp98SourceCoarseBondPath_length] using
      norm_cmp98ContourFirstVariation_zero_le_sourceSupNorm U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b)
  unfold cmp98Eq119NonlinearBlockPhysicalVariation
  change ‖EV * C + E * CV‖ ≤ _
  calc
    ‖EV * C + E * CV‖ ≤ ‖EV‖ * ‖C‖ + ‖E‖ * ‖CV‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤
        (expDerivativeBudget R * nearLogDerivativeBudget r * m * S) * 1 +
          O * ((M : ℝ) * S) := by
      apply add_le_add
      · exact mul_le_mul hEV (le_of_eq hC) (norm_nonneg C)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (expDerivativeBudget_nonneg R
                  (cmp102SourceLogAverageRadius_nonneg
                    ((by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13)))
                (nearLogDerivativeBudget_nonneg r
                  ((by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13)))
              (by positivity))
            (cmp98SourceFieldSupNorm_nonneg A))
      · exact mul_le_mul hE hCV (norm_nonneg CV)
          ((norm_nonneg E).trans hE)
    _ = cmp102PhysicalBlockDerivativeLinearBudget d M r * S := by
      unfold cmp102PhysicalBlockDerivativeLinearBudget R m O
      ring

/-- The literal pre-normalized CMP98 block derivative is background-Lipschitz
with a volume-independent source-scale coefficient. -/
theorem
    norm_cmp98Eq119NonlinearBlockPhysicalVariation_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε r : ℝ) (hε : 0 ≤ ε) (hr13 : 1 / 3 ≤ r) (hr1 : r < 1)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hbaseU : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hbase0 : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix
        (trivialPhysicalGaugeBackground d (M * N') Nc) b x 0‖ ≤ 1 / 3) :
    ‖cmp98Eq119NonlinearBlockPhysicalVariation U A b -
        cmp98Eq119NonlinearBlockPhysicalVariation
          (trivialPhysicalGaugeBackground d (M * N') Nc) A b‖ ≤
      cmp102PhysicalBlockDerivativeBackgroundBudget d M r ε *
        cmp98SourceFieldSupNorm A := by
  let U0 := trivialPhysicalGaugeBackground d (M * N') Nc
  let EU := cmp98UbarExpAverage U b 0
  let E0 := cmp98UbarExpAverage U0 b 0
  let EVU := cmp98UbarExpAveragePhysicalVariation U A b
  let EV0 := cmp98UbarExpAveragePhysicalVariation U0 A b
  let CU := cmp98ContourMatrixCurve U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let C0 := cmp98ContourMatrixCurve U0 A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let CVU := cmp98ContourFirstVariation U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let CV0 := cmp98ContourFirstVariation U0 A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let R := cmp102SourceLogAverageRadius r
  let m : ℝ := ((2 * (d + 1) * M : ℕ) : ℝ)
  let O := cmp98SourceOuterExpNormBudget r
  let S := cmp98SourceFieldSupNorm A
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hEVdiff : ‖EVU - EV0‖ ≤
      cmp102PhysicalExpAverageBackgroundDerivativeBudget d M r ε * S := by
    simpa only [EVU, EV0, U0, S] using
      norm_cmp98UbarExpAveragePhysicalVariation_sub_trivial_le_sourceScale
        U ε r hε hr13 hr1 hsmall A b hbaseU hbase0
  have hEV0 : ‖EV0‖ ≤
      expDerivativeBudget R * nearLogDerivativeBudget r * m * S := by
    simpa only [EV0, U0, R, m, S] using
      norm_cmp98UbarExpAveragePhysicalVariation_le_sourceScale
        U0 A b r hbase0 hr13 hr1
  have hCU : ‖CU‖ = 1 := by
    exact norm_cmp98ContourMatrixCurve_eq_one U A _ 0
  have hCdiff : ‖CU - C0‖ ≤ (M : ℝ) * ε := by
    simpa only [CU, C0, U0] using
      norm_cmp98SourceCoarseContour_zero_sub_trivial_le
        U ε hε hsmall A b
  have hEdiff : ‖EU - E0‖ ≤
      cmp102PhysicalExpAverageBackgroundValueBudget d M r ε := by
    simpa only [EU, E0, U0] using
      norm_cmp98UbarExpAverage_zero_sub_trivial_le_sourceScale
        U ε r hε hr13 hr1 hsmall b hbaseU hbase0
  have hE0 : ‖E0‖ ≤ O := by
    simpa only [E0, U0, O] using
      norm_cmp98UbarExpAverage_zero_le_sourceBudget
        U0 b r hbase0 hr13 hr1
  have hCVU : ‖CVU‖ ≤ (M : ℝ) * S := by
    simpa only [CVU, S, cmp98SourceCoarseBondPath_length] using
      norm_cmp98ContourFirstVariation_zero_le_sourceSupNorm U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b)
  have hCVdiff : ‖CVU - CV0‖ ≤
      (M : ℝ) ^ 2 * ε * S := by
    simpa only [CVU, CV0, U0, S] using
      norm_cmp98SourceCoarseContourFirstVariation_zero_sub_trivial_le
        U ε hε hsmall A b
  have halg :
      (EVU * CU + EU * CVU) - (EV0 * C0 + E0 * CV0) =
        (EVU - EV0) * CU + EV0 * (CU - C0) +
          (EU - E0) * CVU + E0 * (CVU - CV0) := by
    noncomm_ring
  unfold cmp98Eq119NonlinearBlockPhysicalVariation
  change ‖(EVU * CU + EU * CVU) - (EV0 * C0 + E0 * CV0)‖ ≤ _
  rw [halg]
  have hS0 : 0 ≤ S := cmp98SourceFieldSupNorm_nonneg A
  have hEVdiff0 :
      0 ≤ cmp102PhysicalExpAverageBackgroundDerivativeBudget d M r ε * S :=
    mul_nonneg
      (cmp102PhysicalExpAverageBackgroundDerivativeBudget_nonneg hr0 hε) hS0
  have hEV00 :
      0 ≤ expDerivativeBudget R * nearLogDerivativeBudget r * m * S := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (expDerivativeBudget_nonneg R
            (cmp102SourceLogAverageRadius_nonneg hr0))
          (nearLogDerivativeBudget_nonneg r hr0))
        (by positivity))
      hS0
  have hEdiff0 :
      0 ≤ cmp102PhysicalExpAverageBackgroundValueBudget d M r ε :=
    cmp102PhysicalExpAverageBackgroundValueBudget_nonneg hr0 hε
  have hO0 : 0 ≤ O := by
    exact cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hr0
  calc
    ‖(EVU - EV0) * CU + EV0 * (CU - C0) +
        (EU - E0) * CVU + E0 * (CVU - CV0)‖
        ≤ ‖EVU - EV0‖ * ‖CU‖ + ‖EV0‖ * ‖CU - C0‖ +
            ‖EU - E0‖ * ‖CVU‖ + ‖E0‖ * ‖CVU - CV0‖ := by
      have hsum1 :
          ‖(EVU - EV0) * CU + EV0 * (CU - C0) +
              (EU - E0) * CVU + E0 * (CVU - CV0)‖ ≤
            ‖(EVU - EV0) * CU + EV0 * (CU - C0) +
              (EU - E0) * CVU‖ + ‖E0 * (CVU - CV0)‖ :=
        norm_add_le _ _
      have hsum2 :
          ‖(EVU - EV0) * CU + EV0 * (CU - C0) +
              (EU - E0) * CVU‖ ≤
            ‖(EVU - EV0) * CU + EV0 * (CU - C0)‖ +
              ‖(EU - E0) * CVU‖ :=
        norm_add_le _ _
      have hsum3 :
          ‖(EVU - EV0) * CU + EV0 * (CU - C0)‖ ≤
            ‖(EVU - EV0) * CU‖ + ‖EV0 * (CU - C0)‖ :=
        norm_add_le _ _
      have hmul1 :
          ‖(EVU - EV0) * CU‖ ≤ ‖EVU - EV0‖ * ‖CU‖ := norm_mul_le _ _
      have hmul2 :
          ‖EV0 * (CU - C0)‖ ≤ ‖EV0‖ * ‖CU - C0‖ := norm_mul_le _ _
      have hmul3 :
          ‖(EU - E0) * CVU‖ ≤ ‖EU - E0‖ * ‖CVU‖ := norm_mul_le _ _
      have hmul4 :
          ‖E0 * (CVU - CV0)‖ ≤ ‖E0‖ * ‖CVU - CV0‖ := norm_mul_le _ _
      linarith
    _ ≤
        (cmp102PhysicalExpAverageBackgroundDerivativeBudget d M r ε * S) *
            1 +
          (expDerivativeBudget R * nearLogDerivativeBudget r * m * S) *
            ((M : ℝ) * ε) +
          cmp102PhysicalExpAverageBackgroundValueBudget d M r ε *
            ((M : ℝ) * S) +
          O * ((M : ℝ) ^ 2 * ε * S) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (mul_le_mul hEVdiff (le_of_eq hCU) (norm_nonneg CU) hEVdiff0)
            (mul_le_mul hEV0 hCdiff (norm_nonneg (CU - C0)) hEV00))
          (mul_le_mul hEdiff hCVU (norm_nonneg CVU) hEdiff0))
        (mul_le_mul hE0 hCVdiff (norm_nonneg (CVU - CV0)) hO0)
    _ = cmp102PhysicalBlockDerivativeBackgroundBudget d M r ε * S := by
      unfold cmp102PhysicalBlockDerivativeBackgroundBudget R m O
      ring

end

end YangMills.RG
