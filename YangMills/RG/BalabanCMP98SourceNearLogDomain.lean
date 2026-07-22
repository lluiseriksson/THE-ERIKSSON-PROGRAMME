/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ContourExponentialTransport
import YangMills.RG.BalabanCMP98Eq123AnalyticRemainder
import YangMills.RG.NearLogLipschitz

/-!
# A source-explicit Mercator domain along the CMP98 physical line

The qualitative analytic proof of CMP98 (123) assumes that every local
four-contour deviation lies in the open Mercator unit ball.  The exact
exponential transport now turns that assumption away from the background
into a scalar source budget.  Starting from the printed one-third margin,
the entire logarithmic block average and its outer exponential are analytic
at every physical parameter for which the volume-independent contour budget
is smaller than two thirds.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98SourceNearLogDomainMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Explicit displacement budget for one complete CMP98 source contour. -/
def cmp98SourceContourDisplacementBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) : ℝ :=
  (2 * (d + 1) * M : ℕ) *
      (2 * (|t| * cmp98SourceFieldSupNorm A)) *
      (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
        (2 * (d + 1) * M)

theorem cmp98SourceContourDisplacementBudget_nonneg
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (t : ℝ) :
    0 ≤ cmp98SourceContourDisplacementBudget A t := by
  unfold cmp98SourceContourDisplacementBudget
  have hq : 0 ≤ |t| * cmp98SourceFieldSupNorm A :=
    mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  positivity

/-- The one-third background margin and a two-thirds source displacement
budget keep every point of the block in the Mercator domain. -/
theorem cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one_of_third
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hbudget : cmp98SourceContourDisplacementBudget A t < 2 / 3) :
    ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))‖ < 1 := by
  intro x hx
  apply norm_cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one
    U A b x hx t (1 / 3)
  · exact hbase x hx
  · exact hsmall
  · change (1 / 3 : ℝ) + cmp98SourceContourDisplacementBudget A t < 1
    linarith

/-- Quantitative source-explicit variation of one literal Mercator summand.
The radius is a genuine common ball for the background and displaced
four-contour deviations, rather than a supplied Lipschitz constant. -/
theorem norm_nearLog_cmp98UbarAmbientDeviationMatrix_physicalLine_sub_zero_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t r : ℝ)
    (hbase : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A))) -
        nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖ ≤
      nearLogDerivativeBudget r *
        cmp98SourceContourDisplacementBudget A t := by
  let Dt := cmp98UbarAmbientDeviationMatrix U b x
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  let D0 := cmp98UbarAmbientDeviationMatrix U b x 0
  have hdisp : ‖Dt - D0‖ ≤ cmp98SourceContourDisplacementBudget A t := by
    simpa [Dt, D0, cmp98SourceContourDisplacementBudget] using
      norm_cmp98UbarAmbientDeviationMatrix_physicalLine_sub_zero_le
        U A b x hx t hsmall
  have hD0 : ‖D0‖ ≤ r := hbase.trans (le_trans (le_add_of_nonneg_right
    (cmp98SourceContourDisplacementBudget_nonneg A t)) hr)
  have hDt : ‖Dt‖ ≤ r := by
    have htri : ‖Dt‖ ≤ ‖Dt - D0‖ + ‖D0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Dt - D0) D0
    have hsum := add_le_add hdisp hbase
    linarith
  have hr0 : 0 ≤ r := (norm_nonneg D0).trans hD0
  exact (norm_nearLog_sub_nearLog_le hr0 hr1 hDt hD0).trans
    (mul_le_mul_of_nonneg_left hdisp
      (nearLogDerivativeBudget_nonneg r hr0))

/-- The normalized block average has the same source-explicit variation
budget as each of its Mercator summands: the exact block cardinality cancels
the `M⁻ᵈ` normalization, so no volume or block-size loss remains. -/
theorem norm_cmp98UbarLogAverage_physicalLine_sub_zero_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A t ≤ r)
    (hr1 : r < 1) :
    ‖cmp98UbarLogAverage U b
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) -
        cmp98UbarLogAverage U b 0‖ ≤
      nearLogDerivativeBudget r *
        cmp98SourceContourDisplacementBudget A t := by
  let C := nearLogDerivativeBudget r *
    cmp98SourceContourDisplacementBudget A t
  have hpoint : ∀ x ∈ blockOf M N' b.1,
      ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x
            (t • physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent A))) -
          nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖ ≤ C := by
    intro x hx
    exact norm_nearLog_cmp98UbarAmbientDeviationMatrix_physicalLine_sub_zero_le
      U A b x hx t r (hbase x hx) hsmall hr hr1
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMd : (M : ℝ) ^ d ≠ 0 := pow_ne_zero d hM
  let Zt : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    t • physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  let St : Matrix (Fin Nc) (Fin Nc) ℂ :=
    ∑ x ∈ blockOf M N' b.1,
      nearLog (cmp98UbarAmbientDeviationMatrix U b x Zt)
  let S0 : Matrix (Fin Nc) (Fin Nc) ℂ :=
    ∑ x ∈ blockOf M N' b.1,
      nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)
  let SD : Matrix (Fin Nc) (Fin Nc) ℂ :=
    ∑ x ∈ blockOf M N' b.1,
      (nearLog (cmp98UbarAmbientDeviationMatrix U b x Zt) -
        nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))
  have hsum : St - S0 = SD := by
    dsimp only [St, S0, SD]
    exact (Finset.sum_sub_distrib
      (fun x => nearLog (cmp98UbarAmbientDeviationMatrix U b x Zt))
      (fun x => nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))).symm
  have havgReal : cmp98UbarLogAverage U b Zt -
        cmp98UbarLogAverage U b 0 = ((M : ℝ) ^ d)⁻¹ • SD := by
    rw [cmp98UbarLogAverage, cmp98UbarLogAverage]
    change ((M : ℝ) ^ d)⁻¹ • St - ((M : ℝ) ^ d)⁻¹ • S0 = _
    calc
      ((M : ℝ) ^ d)⁻¹ • St - ((M : ℝ) ^ d)⁻¹ • S0 =
          ((M : ℝ) ^ d)⁻¹ • (St - S0) :=
        (smul_sub ((M : ℝ) ^ d)⁻¹ St S0).symm
      _ = ((M : ℝ) ^ d)⁻¹ • SD := congrArg _ hsum
  have hrealComplex : ((M : ℝ) ^ d)⁻¹ • SD =
      (((M : ℝ) ^ d)⁻¹ : ℂ) • SD := by
    ext i j
    simp [RCLike.real_smul_eq_coe_mul]
  have havg : cmp98UbarLogAverage U b
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) -
        cmp98UbarLogAverage U b 0 =
      (((M : ℝ) ^ d)⁻¹ : ℂ) •
        ∑ x ∈ blockOf M N' b.1,
          (nearLog (cmp98UbarAmbientDeviationMatrix U b x
              (t • physicalSuTangentToAmbient
                (physicalCochainToSuMatrixTangent A))) -
            nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)) := by
    simpa only [Zt, SD] using havgReal.trans hrealComplex
  have hnormc : ‖(((M : ℝ) ^ d)⁻¹ : ℂ)‖ = ((M : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg M)]
  rw [havg, norm_smul, hnormc]
  calc
    ((M : ℝ) ^ d)⁻¹ *
          ‖∑ x ∈ blockOf M N' b.1,
            (nearLog (cmp98UbarAmbientDeviationMatrix U b x
                (t • physicalSuTangentToAmbient
                  (physicalCochainToSuMatrixTangent A))) -
              nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))‖
        ≤ ((M : ℝ) ^ d)⁻¹ *
          ∑ x ∈ blockOf M N' b.1,
            ‖nearLog (cmp98UbarAmbientDeviationMatrix U b x
                (t • physicalSuTangentToAmbient
                  (physicalCochainToSuMatrixTangent A))) -
              nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ((M : ℝ) ^ d)⁻¹ * ∑ _x ∈ blockOf M N' b.1, C := by
      gcongr with x hx
      exact hpoint x hx
    _ = C := by
      rw [Finset.sum_const, blockOf_card]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ hMd, one_mul]
    _ = nearLogDerivativeBudget r *
        cmp98SourceContourDisplacementBudget A t := rfl

/-- Source-explicit analyticity of the literal logarithmic block average at
an arbitrary physical parameter. -/
theorem analyticAt_cmp98UbarLogAverage_physicalLine_of_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hbudget : cmp98SourceContourDisplacementBudget A t < 2 / 3) :
    AnalyticAt ℝ
      (fun s : ℝ => cmp98UbarLogAverage U b
        (s • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))) t := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : AnalyticAt ℝ (fun s : ℝ => s • V) t :=
    analyticAt_id.smul analyticAt_const
  have hlog := analyticAt_cmp98UbarLogAverage_of_norm_lt_one
    U b (t • V)
      (cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one_of_third
        U A b t hbase hsmall hbudget)
  simpa [V, Function.comp_def] using hlog.comp_of_eq' hline rfl

/-- Source-explicit analyticity of the outer exponential appearing in the
represented nonlinear block of CMP98 (118)--(119). -/
theorem analyticAt_cmp98UbarExpAverage_physicalLine_of_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hbudget : cmp98SourceContourDisplacementBudget A t < 2 / 3) :
    AnalyticAt ℝ
      (fun s : ℝ => cmp98UbarExpAverage U b
        (s • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))) t := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : AnalyticAt ℝ (fun s : ℝ => s • V) t :=
    analyticAt_id.smul analyticAt_const
  have hexp := analyticAt_cmp98UbarExpAverage_of_norm_lt_one
    U b (t • V)
      (cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one_of_third
        U A b t hbase hsmall hbudget)
  simpa [V, Function.comp_def] using hexp.comp_of_eq' hline rfl

end

end YangMills.RG
