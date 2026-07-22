/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq124Eq125RightNormalization

/-!
# The exact nonlinear logarithmic jet behind CMP98 (122)

The source curve used to derive (118)--(120) records only its first-order
model.  Here we instead return to the literal nonlinear represented block,
normalize it by its exact value at the background, and apply the Mercator
logarithm.  The resulting coordinate is based at zero and its derivative is
the physical right variation already identified with the four sources of
(119).

The final remainder theorem states the exact vanishing of the zeroth and
first jets.  It deliberately does not claim the uniform quadratic norm
estimate of (123); that requires a quantitative second-derivative bound for
the full physical curve.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq122NonlinearLogJetMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The literal nonlinear block of (118), normalized on the right by its
exact background inverse and expressed in deviation coordinates. -/
def cmp98Eq119NonlinearRelativeDeviation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119NonlinearBlockCurve U A b t *
      cmp98Eq119NonlinearBlockInverseAtZero U A b - 1

/-- The exact local logarithmic coordinate of the normalized nonlinear
block. -/
def cmp98Eq119NonlinearLogCoordinate
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  nearLog (cmp98Eq119NonlinearRelativeDeviation U A b t)

@[simp] theorem cmp98Eq119NonlinearRelativeDeviation_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119NonlinearRelativeDeviation U A b 0 = 0 := by
  unfold cmp98Eq119NonlinearRelativeDeviation
  rw [cmp98Eq119NonlinearBlockCurve_zero_mul_inverseAtZero]
  exact sub_self 1

@[simp] theorem cmp98Eq119NonlinearLogCoordinate_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119NonlinearLogCoordinate U A b 0 = 0 := by
  simp [cmp98Eq119NonlinearLogCoordinate]

/-- Exact derivative of the normalized deviation before applying the local
logarithm. -/
theorem hasDerivAt_cmp98Eq119NonlinearRelativeDeviation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    HasDerivAt (cmp98Eq119NonlinearRelativeDeviation U A b)
      (fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
          (cmp98Eq119NonlinearFactorVariations U A b) 0 *
        cmp98Eq119NonlinearBlockInverseAtZero U A b) 0 := by
  have hblock := hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall
  have hmul := hblock.mul_const
    (cmp98Eq119NonlinearBlockInverseAtZero U A b)
  have hsub := hmul.sub_const (1 : Matrix (Fin Nc) (Fin Nc) ℂ)
  simpa only [cmp98Eq119NonlinearRelativeDeviation] using hsub

/-- Applying the logarithm does not change the first derivative because the
relative deviation is exactly zero at the background. -/
theorem hasDerivAt_cmp98Eq119NonlinearLogCoordinate
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    HasDerivAt (cmp98Eq119NonlinearLogCoordinate U A b)
      (fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
          (cmp98Eq119NonlinearFactorVariations U A b) 0 *
        cmp98Eq119NonlinearBlockInverseAtZero U A b) 0 := by
  have hdev := hasDerivAt_cmp98Eq119NonlinearRelativeDeviation U A b hsmall
  have hlog := HasFDerivAt.nearLog_of_eq_zero hdev.hasFDerivAt
    (cmp98Eq119NonlinearRelativeDeviation_zero U A b)
  have h := hlog.hasDerivAt
  convert h using 1
  exact (ContinuousLinearMap.toSpanSingleton_apply_one ℝ
    (fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
        (cmp98Eq119NonlinearFactorVariations U A b) 0 *
      cmp98Eq119NonlinearBlockInverseAtZero U A b)).symm

/-- The derivative of the exact nonlinear log coordinate is the previously
constructed physical right variation. -/
theorem deriv_cmp98Eq119NonlinearLogCoordinate_zero_eq_rightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    deriv (cmp98Eq119NonlinearLogCoordinate U A b) 0 =
      cmp98Eq119NonlinearRightVariation U A b := by
  rw [(hasDerivAt_cmp98Eq119NonlinearLogCoordinate U A b hsmall).deriv]
  unfold cmp98Eq119NonlinearRightVariation
  rw [(hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall).deriv]

/-- The exact nonlinear logarithmic remainder after subtracting its physical
linear right variation. -/
def cmp98Eq122NonlinearLogRemainder
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119NonlinearLogCoordinate U A b t -
    t • cmp98Eq119NonlinearRightVariation U A b

@[simp] theorem cmp98Eq122NonlinearLogRemainder_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq122NonlinearLogRemainder U A b 0 = 0 := by
  unfold cmp98Eq122NonlinearLogRemainder
  rw [cmp98Eq119NonlinearLogCoordinate_zero]
  have hz : (0 : ℝ) • cmp98Eq119NonlinearRightVariation U A b = 0 :=
    zero_smul ℝ _
  rw [hz, sub_zero]

/-- The remainder has zero first derivative: its Taylor expansion begins
strictly after the linear term. -/
theorem hasDerivAt_cmp98Eq122NonlinearLogRemainder_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    HasDerivAt (cmp98Eq122NonlinearLogRemainder U A b) 0 0 := by
  have hlog := hasDerivAt_cmp98Eq119NonlinearLogCoordinate U A b hsmall
  have hline : HasDerivAt
      (fun t : ℝ => t • cmp98Eq119NonlinearRightVariation U A b)
      (cmp98Eq119NonlinearRightVariation U A b) 0 := by
    have hraw := (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
      (cmp98Eq119NonlinearRightVariation U A b)
    have hone : (1 : ℝ) • cmp98Eq119NonlinearRightVariation U A b =
        cmp98Eq119NonlinearRightVariation U A b := by
      ext i j
      simp
    exact hraw.congr_deriv hone
  have hderiv :
      fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
            (cmp98Eq119NonlinearFactorVariations U A b) 0 *
          cmp98Eq119NonlinearBlockInverseAtZero U A b =
        cmp98Eq119NonlinearRightVariation U A b := by
    unfold cmp98Eq119NonlinearRightVariation
    rw [(hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall).deriv]
  rw [hderiv] at hlog
  simpa only [cmp98Eq122NonlinearLogRemainder, sub_self] using hlog.sub hline

end

end YangMills.RG
