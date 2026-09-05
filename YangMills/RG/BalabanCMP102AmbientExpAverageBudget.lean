/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientLogAverageBudget
import YangMills.RG.BalabanCMP102PhysicalTwoFieldExponential

/-!
# Generated outer-exponential budgets for the CMP98 block average

This module propagates the exact normalized logarithmic-average estimates
through the outer noncommutative exponential.  All value and derivative
constants are explicit functions of the source contour radius and the
Mercator radius; none is supplied independently by the caller.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102AmbientExpAverageMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

local instance cmp102AmbientExpAverageCLMNorm :
    Norm (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
      Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102AmbientExpAverageCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102AmbientExpAverageCLMNormedSpace :
    NormedSpace ℝ
      (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.toNormedSpace

/-- Radius of the normalized logarithmic average generated from the local
Mercator ball. -/
def cmp102SourceLogAverageRadius (q : ℝ) : ℝ :=
  cmp102SourceLocalNearLogValueBudget q

/-- Generated value budget for the outer exponential. -/
def cmp102SourceExpAverageValueBudget (q : ℝ) : ℝ :=
  let R := cmp102SourceLogAverageRadius q
  1 + expSecondDerivativeBudget R * R ^ 2 +
    expDerivativeBudget R * R

/-- Generated derivative budget for the outer exponential. -/
def cmp102SourceExpAverageDerivativeBudget
    (d M : ℕ) (r q : ℝ) : ℝ :=
  expDerivativeBudget (cmp102SourceLogAverageRadius q) *
    cmp102SourceLocalNearLogDerivativeBudget d M r q

/-- Generated value-Lipschitz budget for the outer exponential. -/
def cmp102SourceExpAverageValueLipschitzBudget
    (d M : ℕ) (r q : ℝ) : ℝ :=
  cmp102ExpLipschitzBudget (cmp102SourceLogAverageRadius q) *
    cmp102SourceLocalNearLogValueLipschitzBudget d M r q

/-- Generated derivative-Lipschitz budget for the outer exponential. -/
def cmp102SourceExpAverageDerivativeLipschitzBudget
    (d M : ℕ) (r q : ℝ) : ℝ :=
  expSecondDerivativeBudget (cmp102SourceLogAverageRadius q) *
      cmp102SourceLocalNearLogValueLipschitzBudget d M r q *
      cmp102SourceLocalNearLogDerivativeBudget d M r q +
    expDerivativeBudget (cmp102SourceLogAverageRadius q) *
      cmp102SourceLocalNearLogDerivativeLipschitzBudget d M r q

theorem cmp102SourceLogAverageRadius_nonneg
    {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ cmp102SourceLogAverageRadius q := by
  unfold cmp102SourceLogAverageRadius
  exact mul_nonneg (nearLogDerivativeBudget_nonneg q hq) hq

/-- The outer exponential value is bounded entirely from the source
Mercator radius. -/
theorem norm_cmp98UbarExpAverage_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q) :
    ‖cmp98UbarExpAverage U b Z‖ ≤
      cmp102SourceExpAverageValueBudget q := by
  have hY : ‖cmp98UbarLogAverage U b Z‖ ≤
      cmp102SourceLogAverageRadius q := by
    exact norm_cmp98UbarLogAverage_le_sourceBudget U b Z hq0 hq1 hD
  simpa [cmp98UbarExpAverage, cmp102SourceExpAverageValueBudget] using
    norm_exp_le_derivativeBudgets
      (cmp102SourceLogAverageRadius_nonneg hq0) hY

/-- The outer exponential derivative is generated from the exponential
derivative and the exact logarithmic-average derivative. -/
theorem norm_fderiv_cmp98UbarExpAverage_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q) :
    ‖fderiv ℝ (cmp98UbarExpAverage U b) Z‖ ≤
      cmp102SourceExpAverageDerivativeBudget d M r q := by
  let Y := cmp98UbarLogAverage U b Z
  let A := fderiv ℝ
    (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
      Matrix (Fin Nc) (Fin Nc) ℂ) Y
  let B := fderiv ℝ (cmp98UbarLogAverage U b) Z
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hD x hx).trans_lt hq1
  have hcomp :
      fderiv ℝ (cmp98UbarExpAverage U b) Z = A.comp B := by
    have hExp :=
      (NormedSpace.exp_analytic (𝕂 := ℝ) Y).differentiableAt.hasFDerivAt
    have hLog :=
      (analyticAt_cmp98UbarLogAverage_of_norm_lt_one U b Z hsmall
        ).differentiableAt.hasFDerivAt
    simpa only [cmp98UbarExpAverage, Function.comp_apply, A, B, Y] using
      (hExp.comp Z hLog).fderiv
  have hY : ‖Y‖ ≤ cmp102SourceLogAverageRadius q := by
    simpa [Y] using
      norm_cmp98UbarLogAverage_le_sourceBudget U b Z hq0 hq1 hD
  have hA : ‖A‖ ≤
      expDerivativeBudget (cmp102SourceLogAverageRadius q) := by
    simpa [A] using norm_fderiv_exp_le_derivativeBudget hY
  have hB : ‖B‖ ≤
      cmp102SourceLocalNearLogDerivativeBudget d M r q := by
    simpa [B] using
      norm_fderiv_cmp98UbarLogAverage_le_sourceBudget
        U b Z hr hq0 hq1 hZ hD
  rw [hcomp]
  calc
    ‖A.comp B‖ ≤ ‖A‖ * ‖B‖ :=
      ContinuousLinearMap.opNorm_comp_le A B
    _ ≤ expDerivativeBudget (cmp102SourceLogAverageRadius q) *
          cmp102SourceLocalNearLogDerivativeBudget d M r q := by
      exact mul_le_mul hA hB (norm_nonneg B)
        (expDerivativeBudget_nonneg _
          (cmp102SourceLogAverageRadius_nonneg hq0))
    _ = cmp102SourceExpAverageDerivativeBudget d M r q := rfl

/-- The outer exponential inherits the exact two-field Lipschitz budget of
the normalized logarithmic average. -/
theorem norm_cmp98UbarExpAverage_sub_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q)
    (hDW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ ≤ q) :
    ‖cmp98UbarExpAverage U b Z - cmp98UbarExpAverage U b W‖ ≤
      cmp102SourceExpAverageValueLipschitzBudget d M r q *
        ‖Z - W‖ := by
  let YZ := cmp98UbarLogAverage U b Z
  let YW := cmp98UbarLogAverage U b W
  have hYZ : ‖YZ‖ ≤ cmp102SourceLogAverageRadius q := by
    simpa [YZ] using
      norm_cmp98UbarLogAverage_le_sourceBudget U b Z hq0 hq1 hDZ
  have hYW : ‖YW‖ ≤ cmp102SourceLogAverageRadius q := by
    simpa [YW] using
      norm_cmp98UbarLogAverage_le_sourceBudget U b W hq0 hq1 hDW
  have hdiff : ‖YZ - YW‖ ≤
      cmp102SourceLocalNearLogValueLipschitzBudget d M r q *
        ‖Z - W‖ := by
    simpa [YZ, YW] using
      norm_cmp98UbarLogAverage_sub_le_sourceBudget
        U b Z W hr hq0 hq1 hZ hW hDZ hDW
  calc
    ‖cmp98UbarExpAverage U b Z - cmp98UbarExpAverage U b W‖ =
        ‖NormedSpace.exp YZ - NormedSpace.exp YW‖ := rfl
    _ ≤ cmp102ExpLipschitzBudget (cmp102SourceLogAverageRadius q) *
          ‖YZ - YW‖ :=
      norm_exp_sub_exp_le_cmp102ExpLipschitzBudget
        (cmp102SourceLogAverageRadius_nonneg hq0) hYZ hYW
    _ ≤ cmp102ExpLipschitzBudget (cmp102SourceLogAverageRadius q) *
          (cmp102SourceLocalNearLogValueLipschitzBudget d M r q *
            ‖Z - W‖) := by
      gcongr
      exact cmp102ExpLipschitzBudget_nonneg _
        (cmp102SourceLogAverageRadius_nonneg hq0)
    _ = cmp102SourceExpAverageValueLipschitzBudget d M r q *
          ‖Z - W‖ := by
      unfold cmp102SourceExpAverageValueLipschitzBudget
      ring

/-- The outer exponential derivative inherits an explicit two-term
Lipschitz budget from its outer derivative and the logarithmic average. -/
theorem norm_fderiv_cmp98UbarExpAverage_sub_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q)
    (hDW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ ≤ q) :
    ‖fderiv ℝ (cmp98UbarExpAverage U b) Z -
        fderiv ℝ (cmp98UbarExpAverage U b) W‖ ≤
      cmp102SourceExpAverageDerivativeLipschitzBudget d M r q *
        ‖Z - W‖ := by
  let YZ := cmp98UbarLogAverage U b Z
  let YW := cmp98UbarLogAverage U b W
  let AZ := fderiv ℝ
    (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
      Matrix (Fin Nc) (Fin Nc) ℂ) YZ
  let AW := fderiv ℝ
    (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
      Matrix (Fin Nc) (Fin Nc) ℂ) YW
  let BZ := fderiv ℝ (cmp98UbarLogAverage U b) Z
  let BW := fderiv ℝ (cmp98UbarLogAverage U b) W
  have hsmallZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hDZ x hx).trans_lt hq1
  have hsmallW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ < 1 :=
    fun x hx => (hDW x hx).trans_lt hq1
  have hcompZ : fderiv ℝ (cmp98UbarExpAverage U b) Z = AZ.comp BZ := by
    have hExp :=
      (NormedSpace.exp_analytic (𝕂 := ℝ) YZ).differentiableAt.hasFDerivAt
    have hLog :=
      (analyticAt_cmp98UbarLogAverage_of_norm_lt_one U b Z hsmallZ
        ).differentiableAt.hasFDerivAt
    simpa only [cmp98UbarExpAverage, Function.comp_apply, AZ, BZ, YZ] using
      (hExp.comp Z hLog).fderiv
  have hcompW : fderiv ℝ (cmp98UbarExpAverage U b) W = AW.comp BW := by
    have hExp :=
      (NormedSpace.exp_analytic (𝕂 := ℝ) YW).differentiableAt.hasFDerivAt
    have hLog :=
      (analyticAt_cmp98UbarLogAverage_of_norm_lt_one U b W hsmallW
        ).differentiableAt.hasFDerivAt
    simpa only [cmp98UbarExpAverage, Function.comp_apply, AW, BW, YW] using
      (hExp.comp W hLog).fderiv
  have htelescope :
      AZ.comp BZ - AW.comp BW =
        (AZ - AW).comp BZ + AW.comp (BZ - BW) := by
    apply ContinuousLinearMap.ext
    intro H
    change AZ (BZ H) - AW (BW H) =
      (AZ (BZ H) - AW (BZ H)) + AW (BZ H - BW H)
    rw [AW.map_sub]
    abel
  have hYZ : ‖YZ‖ ≤ cmp102SourceLogAverageRadius q := by
    simpa [YZ] using
      norm_cmp98UbarLogAverage_le_sourceBudget U b Z hq0 hq1 hDZ
  have hYW : ‖YW‖ ≤ cmp102SourceLogAverageRadius q := by
    simpa [YW] using
      norm_cmp98UbarLogAverage_le_sourceBudget U b W hq0 hq1 hDW
  have hAZAW : ‖AZ - AW‖ ≤
      expSecondDerivativeBudget (cmp102SourceLogAverageRadius q) *
        (cmp102SourceLocalNearLogValueLipschitzBudget d M r q *
          ‖Z - W‖) := by
    have hYdiff : ‖YZ - YW‖ ≤
        cmp102SourceLocalNearLogValueLipschitzBudget d M r q *
          ‖Z - W‖ := by
      simpa [YZ, YW] using
        norm_cmp98UbarLogAverage_sub_le_sourceBudget
          U b Z W hr hq0 hq1 hZ hW hDZ hDW
    exact
      (norm_fderiv_exp_sub_le_secondDerivativeBudget hYZ hYW).trans
        (mul_le_mul_of_nonneg_left hYdiff
          (expSecondDerivativeBudget_nonneg _
            (cmp102SourceLogAverageRadius_nonneg hq0)))
  have hBZ : ‖BZ‖ ≤
      cmp102SourceLocalNearLogDerivativeBudget d M r q := by
    simpa [BZ] using
      norm_fderiv_cmp98UbarLogAverage_le_sourceBudget
        U b Z hr hq0 hq1 hZ hDZ
  have hAW : ‖AW‖ ≤
      expDerivativeBudget (cmp102SourceLogAverageRadius q) := by
    simpa [AW] using norm_fderiv_exp_le_derivativeBudget hYW
  have hBZBW : ‖BZ - BW‖ ≤
      cmp102SourceLocalNearLogDerivativeLipschitzBudget d M r q *
        ‖Z - W‖ := by
    simpa [BZ, BW] using
      norm_fderiv_cmp98UbarLogAverage_sub_le_sourceBudget
        U b Z W hr hq0 hq1 hZ hW hDZ hDW
  rw [hcompZ, hcompW, htelescope]
  calc
    ‖(AZ - AW).comp BZ + AW.comp (BZ - BW)‖
        ≤ ‖(AZ - AW).comp BZ‖ + ‖AW.comp (BZ - BW)‖ :=
      norm_add_le ((AZ - AW).comp BZ) (AW.comp (BZ - BW))
    _ ≤ ‖AZ - AW‖ * ‖BZ‖ + ‖AW‖ * ‖BZ - BW‖ := by
      gcongr
      · exact ContinuousLinearMap.opNorm_comp_le _ _
      · exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤
        (expSecondDerivativeBudget (cmp102SourceLogAverageRadius q) *
            (cmp102SourceLocalNearLogValueLipschitzBudget d M r q *
              ‖Z - W‖)) *
            cmp102SourceLocalNearLogDerivativeBudget d M r q +
          expDerivativeBudget (cmp102SourceLogAverageRadius q) *
            (cmp102SourceLocalNearLogDerivativeLipschitzBudget d M r q *
              ‖Z - W‖) := by
      apply add_le_add
      · exact mul_le_mul hAZAW hBZ (norm_nonneg BZ)
          (mul_nonneg
            (expSecondDerivativeBudget_nonneg _
              (cmp102SourceLogAverageRadius_nonneg hq0))
            (mul_nonneg
              (mul_nonneg (nearLogDerivativeBudget_nonneg q hq0)
                (cmp98AmbientWilsonLineValueLipschitzBudget_nonneg hr _))
              (norm_nonneg _)))
      · exact mul_le_mul hAW hBZBW (norm_nonneg (BZ - BW))
          (expDerivativeBudget_nonneg _
            (cmp102SourceLogAverageRadius_nonneg hq0))
    _ = cmp102SourceExpAverageDerivativeLipschitzBudget d M r q *
          ‖Z - W‖ := by
      unfold cmp102SourceExpAverageDerivativeLipschitzBudget
      ring

end

end YangMills.RG
