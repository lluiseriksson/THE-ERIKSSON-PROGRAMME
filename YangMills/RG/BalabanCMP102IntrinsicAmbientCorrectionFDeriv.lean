/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientNonlinearBlockFDeriv
import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionAnalytic
import YangMills.RG.NoncommutativePowerLipschitz

/-!
# Derivative of the intrinsic CMP102 ambient correction

The intrinsic equation-(122) correction is a Mercator logarithm of the
literal nonlinear represented block, minus its fixed linearization at the
origin.  This file differentiates that expression without replacing either
factor by an abstract Hessian certificate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102IntrinsicAmbientFDerivMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Exact first derivative of the literal intrinsic ambient correction.
The fixed subtraction differentiates to the derivative of the represented
block at the origin, while the nonlinear term retains the derivative of
the represented block at the current field. -/
theorem fderiv_cmp102IntrinsicAmbientCorrectionBond_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z H : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hlocal : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hrelative :
      ‖cmp102AmbientNonlinearBlock U b Z *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1) :
    fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) Z H =
      fderiv ℝ nearLog
          (cmp102AmbientNonlinearBlock U b Z *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1)
          (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b) -
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 H *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  let I :=
    cmp98Eq119NonlinearBlockInverseAtZero U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b
  have hblock :
      DifferentiableAt ℝ (cmp102AmbientNonlinearBlock U b) Z := by
    unfold cmp102AmbientNonlinearBlock
    exact
      (analyticAt_cmp98UbarExpAverage_of_norm_lt_one U b Z hlocal).differentiableAt.mul
        (analyticAt_cmp98AmbientWilsonLineMatrix U Z
          (cmp98SourceCoarseBondPath (Nc := Nc) b)).differentiableAt
  have hdev :
      DifferentiableAt ℝ
        (fun W => cmp102AmbientNonlinearBlock U b W * I - 1) Z :=
    (hblock.mul_const I).sub_const 1
  have hnear :
      DifferentiableAt ℝ nearLog
        (cmp102AmbientNonlinearBlock U b Z * I - 1) :=
    (analyticAt_nearLog_of_norm_lt_one
      (by simpa [I] using hrelative)).differentiableAt
  have hlog :
      DifferentiableAt ℝ
        (fun W => nearLog
          (cmp102AmbientNonlinearBlock U b W * I - 1)) Z :=
    by
      simpa only [Function.comp_apply] using hnear.comp Z hdev
  have hlinear :
      DifferentiableAt ℝ
        (fun W =>
          fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W * I) Z :=
    (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0).differentiableAt.mul_const I
  unfold cmp102IntrinsicAmbientCorrectionBond
  dsimp only
  change
    fderiv ℝ
        (fun W =>
          nearLog (cmp102AmbientNonlinearBlock U b W * I - 1) -
            fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W * I)
        Z H =
      fderiv ℝ nearLog
          (cmp102AmbientNonlinearBlock U b Z * I - 1)
          (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H * I) -
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 H * I
  rw [show
    (fun W =>
      nearLog (cmp102AmbientNonlinearBlock U b W * I - 1) -
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W * I) =
      (fun W => nearLog
        (cmp102AmbientNonlinearBlock U b W * I - 1)) -
      (fun W =>
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W * I) by rfl]
  rw [fderiv_sub hlog hlinear, ContinuousLinearMap.sub_apply]
  rw [show
    (fun W => nearLog
      (cmp102AmbientNonlinearBlock U b W * I - 1)) =
      nearLog ∘
        (fun W => cmp102AmbientNonlinearBlock U b W * I - 1) by rfl]
  rw [fderiv_comp Z hnear hdev, ContinuousLinearMap.comp_apply]
  rw [fderiv_sub_const]
  have hmul :
      fderiv ℝ
          (fun W => cmp102AmbientNonlinearBlock U b W * I) Z H =
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H * I := by
    have hmap := congrArg (fun L => L H)
      (fderiv_mul_const' hblock I)
    simpa only [ContinuousLinearMap.fderiv, Pi.smul_apply,
      op_smul_eq_mul] using hmap
  have hlinearApply :
      fderiv ℝ
          (fun W =>
            fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 W * I) Z H =
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 H * I := by
    let R :
        Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ]
          Matrix (Fin Nc) (Fin Nc) ℂ :=
      (ContinuousLinearMap.mul ℝ
        (Matrix (Fin Nc) (Fin Nc) ℂ)).flip I
    let L :=
      fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
    rw [show
      (fun W => L W * I) = (R.comp L : _ → _) by
        funext W
        rfl]
    have hRL :
        fderiv ℝ
            ((R.comp L :
              PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
                Matrix (Fin Nc) (Fin Nc) ℂ) : _ → _) Z =
          R.comp L :=
      (R.comp L).hasFDerivAt.fderiv
    rw [hRL]
    rfl
  rw [hmul, hlinearApply]

/-- Exact two-point decomposition of the derivative variation.  The fixed
linear subtraction cancels.  What remains is the sum of:

* variation of the Mercator derivative at a fixed block derivative;
* variation of the represented-block derivative passed through the second
  Mercator derivative.

This is the quantitative factorization needed before inserting the
audited `nearLog` derivative-Lipschitz budget. -/
theorem fderiv_cmp102IntrinsicAmbientCorrectionBond_sub_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W H : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hlocalZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hrelativeZ :
      ‖cmp102AmbientNonlinearBlock U b Z *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1)
    (hlocalW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ < 1)
    (hrelativeW :
      ‖cmp102AmbientNonlinearBlock U b W *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1) :
    (fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) Z -
        fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) W) H =
      (fderiv ℝ nearLog
          (cmp102AmbientNonlinearBlock U b Z *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1) -
        fderiv ℝ nearLog
          (cmp102AmbientNonlinearBlock U b W *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1))
          (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b) +
        fderiv ℝ nearLog
          (cmp102AmbientNonlinearBlock U b W *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1)
          ((fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
              fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b) := by
  rw [ContinuousLinearMap.sub_apply]
  rw [fderiv_cmp102IntrinsicAmbientCorrectionBond_apply
      U b Z H hlocalZ hrelativeZ,
    fderiv_cmp102IntrinsicAmbientCorrectionBond_apply
      U b W H hlocalW hrelativeW]
  have hinput :
      ((fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
          fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : PhysicalGaugeOneCochain d (M * N') Nc) b) =
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b -
          fderiv ℝ (cmp102AmbientNonlinearBlock U b) W H *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b := by
    rw [ContinuousLinearMap.sub_apply, sub_mul]
  rw [hinput,
    (fderiv ℝ nearLog
      (cmp102AmbientNonlinearBlock U b W *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1)).map_sub]
  simp only [ContinuousLinearMap.sub_apply]
  abel

/-- Explicit budget obtained after the Mercator derivative is discharged.
The four remaining parameters respectively bound the relative-deviation
Lipschitz rate, the represented-block derivative, its Lipschitz rate, and
the fixed right normalizer. -/
def cmp102IntrinsicAmbientCorrectionDerivativeLipschitzBudget
    (r Ldev Lblock LblockDeriv K : ℝ) : ℝ :=
  nearLogSecondDerivativeBudget r * Ldev * Lblock * K +
    nearLogDerivativeBudget r * LblockDeriv * K

/-- Quantitative consequence of the exact derivative factorization.  Both
Mercator contributions are generated internally from their audited series
budgets.  The only residual analytic inputs concern the literal represented
block and its fixed right normalizer. -/
theorem norm_fderiv_cmp102IntrinsicAmbientCorrectionBond_sub_apply_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W H : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r Ldev Lblock LblockDeriv K : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hLdev : 0 ≤ Ldev) (hLblock : 0 ≤ Lblock)
    (hLblockDeriv : 0 ≤ LblockDeriv)
    (hlocalZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hlocalW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ < 1)
    (hdevZ :
      ‖cmp102AmbientNonlinearBlock U b Z *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ ≤ r)
    (hdevW :
      ‖cmp102AmbientNonlinearBlock U b W *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ ≤ r)
    (hdevDiff :
      ‖(cmp102AmbientNonlinearBlock U b Z *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1) -
          (cmp102AmbientNonlinearBlock U b W *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1)‖ ≤
        Ldev * ‖Z - W‖)
    (hblock :
      ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z‖ ≤ Lblock)
    (hblockDeriv :
      ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
          fderiv ℝ (cmp102AmbientNonlinearBlock U b) W‖ ≤
        LblockDeriv * ‖Z - W‖)
    (hI :
      ‖cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : PhysicalGaugeOneCochain d (M * N') Nc) b‖ ≤ K) :
    ‖(fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) Z -
        fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) W) H‖ ≤
      cmp102IntrinsicAmbientCorrectionDerivativeLipschitzBudget
          r Ldev Lblock LblockDeriv K *
        ‖Z - W‖ * ‖H‖ := by
  let I :=
    cmp98Eq119NonlinearBlockInverseAtZero U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b
  let DZ :=
    cmp102AmbientNonlinearBlock U b Z * I - 1
  let DW :=
    cmp102AmbientNonlinearBlock U b W * I - 1
  have hrelativeZ : ‖DZ‖ < 1 := by
    exact (show ‖DZ‖ ≤ r by simpa [DZ, I] using hdevZ).trans_lt hr1
  have hrelativeW : ‖DW‖ < 1 := by
    exact (show ‖DW‖ ≤ r by simpa [DW, I] using hdevW).trans_lt hr1
  have hlogDiff :
      ‖fderiv ℝ nearLog DZ - fderiv ℝ nearLog DW‖ ≤
        nearLogSecondDerivativeBudget r * (Ldev * ‖Z - W‖) := by
    calc
      ‖fderiv ℝ nearLog DZ - fderiv ℝ nearLog DW‖
          ≤ nearLogSecondDerivativeBudget r * ‖DZ - DW‖ :=
        norm_fderiv_nearLog_sub_le_secondDerivativeBudget
          hr0 hr1 (by simpa [DZ, I] using hdevZ)
            (by simpa [DW, I] using hdevW)
      _ ≤ nearLogSecondDerivativeBudget r * (Ldev * ‖Z - W‖) := by
        gcongr
        exact nearLogSecondDerivativeBudget_nonneg r hr0
  have hlogW :
      ‖fderiv ℝ nearLog DW‖ ≤ nearLogDerivativeBudget r :=
    norm_fderiv_nearLog_le_derivativeBudget
      hr0 hr1 (by simpa [DW, I] using hdevW)
  have hblockApply :
      ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H * I‖ ≤
        (Lblock * ‖H‖) * K := by
    calc
      ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H * I‖
          ≤ ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H‖ * ‖I‖ :=
        norm_mul_le _ _
      _ ≤ (‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z‖ * ‖H‖) *
            ‖I‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ H
      _ ≤ (Lblock * ‖H‖) * K := by
        gcongr
  have hblockDerivApply :
      ‖(fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
          fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H * I‖ ≤
        ((LblockDeriv * ‖Z - W‖) * ‖H‖) * K := by
    calc
      ‖(fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
          fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H * I‖
          ≤ ‖(fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
              fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H‖ * ‖I‖ :=
        norm_mul_le _ _
      _ ≤ (‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
              fderiv ℝ (cmp102AmbientNonlinearBlock U b) W‖ * ‖H‖) *
            ‖I‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ H
      _ ≤ ((LblockDeriv * ‖Z - W‖) * ‖H‖) * K := by
        gcongr
  rw [fderiv_cmp102IntrinsicAmbientCorrectionBond_sub_apply
    U b Z W H hlocalZ hrelativeZ hlocalW hrelativeW]
  calc
    ‖(fderiv ℝ nearLog DZ - fderiv ℝ nearLog DW)
          (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H * I) +
        fderiv ℝ nearLog DW
          ((fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
            fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H * I)‖
        ≤ ‖(fderiv ℝ nearLog DZ - fderiv ℝ nearLog DW)
              (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H * I)‖ +
            ‖fderiv ℝ nearLog DW
              ((fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
                fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H * I)‖ :=
          norm_add_le _ _
    _ ≤ ‖fderiv ℝ nearLog DZ - fderiv ℝ nearLog DW‖ *
            ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H * I‖ +
          ‖fderiv ℝ nearLog DW‖ *
            ‖(fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
              fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H * I‖ := by
        gcongr
        · exact ContinuousLinearMap.le_opNorm _ _
        · exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (nearLogSecondDerivativeBudget r * (Ldev * ‖Z - W‖)) *
            ((Lblock * ‖H‖) * K) +
          nearLogDerivativeBudget r *
            (((LblockDeriv * ‖Z - W‖) * ‖H‖) * K) := by
        gcongr
        · exact mul_nonneg
            (nearLogSecondDerivativeBudget_nonneg r hr0)
            (mul_nonneg hLdev (norm_nonneg _))
        · exact nearLogDerivativeBudget_nonneg r hr0
    _ = cmp102IntrinsicAmbientCorrectionDerivativeLipschitzBudget
          r Ldev Lblock LblockDeriv K * ‖Z - W‖ * ‖H‖ := by
        unfold cmp102IntrinsicAmbientCorrectionDerivativeLipschitzBudget
        ring

end

end YangMills.RG
