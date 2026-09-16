/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq124Eq125Bridge
import YangMills.RG.BalabanCMP116FourFactorSecondDerivative

/-!
# The literal nonlinear block behind CMP98 (118)--(119)

CMP98 (118) expands the represented block

`exp (block-log-average) * coarse-holonomy`.

This file differentiates that literal product along a physical gauge-field
line and right-trivializes by its two exact inverse factors.  Consequently the
sign of the outer `g(ad)` operator is fixed by the noncommutative exponential
derivative, rather than by a coordinate convention or a supplied identity.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq119NonlinearMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The exact represented block in (118), along the physical tangent line:
the exponential of the literal logarithmic block average followed by the
literal straight coarse-bond holonomy. -/
def cmp98Eq119NonlinearBlockCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98UbarExpAverage U b
      (t • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A)) *
    cmp98ContourMatrixCurve U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b) t

/-- Derivative of the exponential factor along the literal physical line. -/
theorem hasDerivAt_cmp98UbarExpAverage_physicalLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    HasDerivAt
      (fun t : ℝ => cmp98UbarExpAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)))
      (fderiv ℝ
          (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
            Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp98UbarLogAverage U b 0)
          (cmp98UbarLogAveragePhysicalVariation U A b)) 0 := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : HasDerivAt (fun t : ℝ => t • V) V 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const V
  have hzero : (0 : ℝ) • V = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  have houterAt : HasFDerivAt (cmp98UbarExpAverage U b)
      ((fderiv ℝ
          (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
            Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp98UbarLogAverage U b 0)).comp
        (fderiv ℝ (cmp98UbarLogAverage U b) 0)) ((0 : ℝ) • V) := by
    rw [hzero]
    exact hasFDerivAt_cmp98UbarExpAverage U b hsmall
  have hcomp := houterAt.comp_hasDerivAt 0 hline
  have hlog : fderiv ℝ (cmp98UbarLogAverage U b) 0 V =
      cmp98UbarLogAveragePhysicalVariation U A b := by
    simpa only [V] using
      fderiv_cmp98UbarLogAverage_zero_apply_physical U A b hsmall
  rw [ContinuousLinearMap.comp_apply, hlog] at hcomp
  simpa [Function.comp_def, V] using hcomp

/-- Four-factor presentation of the literal nonlinear block.  The last two
factors are identities; this lets us reuse the already compiled
noncommutative product rule without changing the represented block. -/
def cmp98Eq119NonlinearFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![fun t => cmp98UbarExpAverage U b
      (t • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A)),
    cmp98ContourMatrixCurve U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b),
    fun _ => 1,
    fun _ => 1]

/-- Claimed first variations of the four-factor presentation. -/
def cmp98Eq119NonlinearFactorVariations
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![fun _ => fderiv ℝ
      (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ)
      (cmp98UbarLogAverage U b 0)
      (cmp98UbarLogAveragePhysicalVariation U A b),
    cmp98ContourFirstVariation U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b),
    fun _ => 0,
    fun _ => 0]

@[simp] theorem cmp98Eq119NonlinearFactors_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactors U A b 0 t =
      cmp98UbarExpAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) := rfl

@[simp] theorem cmp98Eq119NonlinearFactors_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactors U A b 1 t =
      cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) t := rfl

@[simp] theorem cmp98Eq119NonlinearFactors_two
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactors U A b 2 t = 1 := rfl

@[simp] theorem cmp98Eq119NonlinearFactors_three
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactors U A b 3 t = 1 := rfl

@[simp] theorem cmp98Eq119NonlinearFactorVariations_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactorVariations U A b 0 t =
      fderiv ℝ
        (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
          Matrix (Fin Nc) (Fin Nc) ℂ)
        (cmp98UbarLogAverage U b 0)
        (cmp98UbarLogAveragePhysicalVariation U A b) := rfl

@[simp] theorem cmp98Eq119NonlinearFactorVariations_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactorVariations U A b 1 t =
      cmp98ContourFirstVariation U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) t := rfl

@[simp] theorem cmp98Eq119NonlinearFactorVariations_two
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactorVariations U A b 2 t = 0 := rfl

@[simp] theorem cmp98Eq119NonlinearFactorVariations_three
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearFactorVariations U A b 3 t = 0 := rfl

/-- Every factor in the four-factor presentation has its claimed derivative
at the background. -/
theorem hasDerivAt_cmp98Eq119NonlinearFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (i : Fin 4) :
    HasDerivAt (cmp98Eq119NonlinearFactors U A b i)
      (cmp98Eq119NonlinearFactorVariations U A b i 0) 0 := by
  fin_cases i
  · exact hasDerivAt_cmp98UbarExpAverage_physicalLine U A b hsmall
  · exact hasDerivAt_cmp98ContourMatrixCurve U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  · simpa only [cmp98Eq119NonlinearFactors,
        cmp98Eq119NonlinearFactorVariations, Matrix.cons_val_two] using
      (hasDerivAt_const (x := (0 : ℝ))
        (c := (1 : Matrix (Fin Nc) (Fin Nc) ℂ)))
  · simpa only [cmp98Eq119NonlinearFactors,
        cmp98Eq119NonlinearFactorVariations, Matrix.cons_val_three] using
      (hasDerivAt_const (x := (0 : ℝ))
        (c := (1 : Matrix (Fin Nc) (Fin Nc) ℂ)))

/-- The padded four-factor curve is literally the represented two-factor
block. -/
theorem cmp98Eq119_fourFactorProduct_eq_nonlinearBlockCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    fourFactorProduct (cmp98Eq119NonlinearFactors U A b) =
      cmp98Eq119NonlinearBlockCurve U A b := by
  funext t
  simp only [fourFactorProduct, cmp98Eq119NonlinearFactors_zero,
    cmp98Eq119NonlinearFactors_one, cmp98Eq119NonlinearFactors_two,
    cmp98Eq119NonlinearFactors_three, cmp98Eq119NonlinearBlockCurve,
    mul_one]

/-- Exact structural product-rule derivative of the represented nonlinear
block. -/
theorem hasDerivAt_cmp98Eq119NonlinearBlockCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    HasDerivAt (cmp98Eq119NonlinearBlockCurve U A b)
      (fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
        (cmp98Eq119NonlinearFactorVariations U A b) 0) 0 := by
  rw [← cmp98Eq119_fourFactorProduct_eq_nonlinearBlockCurve U A b]
  exact hasDerivAt_fourFactorProduct
    (cmp98Eq119NonlinearFactors U A b)
    (cmp98Eq119NonlinearFactorVariations U A b) 0
    (hasDerivAt_cmp98Eq119NonlinearFactors U A b hsmall)

/-- The structural derivative reduces to the familiar two-factor product
rule.  Keeping this normalization separate from differentiation avoids any
hidden analytic input. -/
theorem cmp98Eq119_fourFactorFirst_eq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    fourFactorFirst (cmp98Eq119NonlinearFactors U A b)
        (cmp98Eq119NonlinearFactorVariations U A b) 0 =
      fderiv ℝ
          (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
            Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp98UbarLogAverage U b 0)
          (cmp98UbarLogAveragePhysicalVariation U A b) *
          cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 +
        cmp98UbarExpAverage U b 0 *
          cmp98ContourFirstVariation U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0 := by
  simp only [fourFactorFirst,
      cmp98Eq119NonlinearFactors_zero, cmp98Eq119NonlinearFactors_one,
      cmp98Eq119NonlinearFactors_two, cmp98Eq119NonlinearFactors_three,
      cmp98Eq119NonlinearFactorVariations_zero,
      cmp98Eq119NonlinearFactorVariations_one,
      cmp98Eq119NonlinearFactorVariations_two,
      cmp98Eq119NonlinearFactorVariations_three,
      mul_one, mul_zero, add_zero]
  have hzero : (0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A) = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  rw [hzero]

/-- The exact two-factor inverse used for right trivialization at the
background: coarse inverse followed by `exp(-Y)`. -/
def cmp98Eq119NonlinearBlockInverseAtZero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  Matrix.conjTranspose
      (cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) *
    NormedSpace.exp (-(cmp98UbarLogAverage U b 0))

/-- Right-trivialized derivative of the literal nonlinear block. -/
def cmp98Eq119NonlinearRightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  deriv (cmp98Eq119NonlinearBlockCurve U A b) 0 *
    cmp98Eq119NonlinearBlockInverseAtZero U A b

/-- The represented block times the two literal inverse factors is exactly
the identity at the background. -/
theorem cmp98Eq119NonlinearBlockCurve_zero_mul_inverseAtZero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119NonlinearBlockCurve U A b 0 *
        cmp98Eq119NonlinearBlockInverseAtZero U A b = 1 := by
  unfold cmp98Eq119NonlinearBlockCurve
    cmp98Eq119NonlinearBlockInverseAtZero cmp98UbarExpAverage
  have hzero : (0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A) = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  rw [hzero]
  rw [mul_assoc, ← mul_assoc
      (cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0),
    cmp98ContourMatrixCurve_zero_mul_conjTranspose_general U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b),
    one_mul, cmp98_exp_mul_exp_neg]

/-- **Sign-deciding nonlinear bridge for CMP98 (118)--(119).**  The exact
right variation of `exp(Y) * U(c)` is the right-trivialized exponential
derivative `g(ad (-Y))`, plus the coarse variation conjugated by `exp(Y)`.
No sign convention is supplied to the theorem. -/
theorem cmp98Eq119NonlinearRightVariation_eq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq119NonlinearRightVariation U A b =
      cmp98GAd (-(cmp98UbarLogAverage U b 0))
          (cmp98UbarLogAveragePhysicalVariation U A b) +
        cmp98Eq119DirectCoarseTransportedVariation U A b := by
  rw [cmp98Eq119NonlinearRightVariation,
    (hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall).deriv,
    cmp98Eq119_fourFactorFirst_eq]
  unfold cmp98Eq119NonlinearBlockInverseAtZero
    cmp98Eq119DirectCoarseTransportedVariation cmp98Eq119CoarseRightVariation
    cmp98UbarExpAverage
  let Y := cmp98UbarLogAverage U b 0
  let H := cmp98UbarLogAveragePhysicalVariation U A b
  let C := cmp98ContourMatrixCurve U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let C' := cmp98ContourFirstVariation U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  change
    (fderiv ℝ (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
          Matrix (Fin Nc) (Fin Nc) ℂ) Y H * C +
        NormedSpace.exp Y * C') *
        (Matrix.conjTranspose C * NormedSpace.exp (-Y)) =
      cmp98GAd (-Y) H +
        NormedSpace.exp Y * (C' * Matrix.conjTranspose C) *
          NormedSpace.exp (-Y)
  have hC : C * Matrix.conjTranspose C = 1 := by
    exact cmp98ContourMatrixCurve_zero_mul_conjTranspose_general U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b)
  rw [add_mul,
    mul_assoc (fderiv ℝ
      (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ) Y H) C,
    ← mul_assoc C (Matrix.conjTranspose C), hC, one_mul]
  calc
    (fderiv ℝ (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
          Matrix (Fin Nc) (Fin Nc) ℂ) Y H * NormedSpace.exp (-Y) +
        NormedSpace.exp Y * C' *
          (Matrix.conjTranspose C * NormedSpace.exp (-Y))) =
      cmp98GAd (-Y) H +
        NormedSpace.exp Y * C' *
          (Matrix.conjTranspose C * NormedSpace.exp (-Y)) := by
            exact congrArg (fun z => z + NormedSpace.exp Y * C' *
              (Matrix.conjTranspose C * NormedSpace.exp (-Y)))
              (cmp98_fderiv_exp_mul_exp_neg_eq_gad_neg_apply Y H)
    _ = cmp98GAd (-Y) H +
        NormedSpace.exp Y * (C' * Matrix.conjTranspose C) *
          NormedSpace.exp (-Y) := by noncomm_ring

end

end YangMills.RG
