/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq119RightSourceBridge

/-!
# A source-faithful first-order curve for CMP98 (118)

The three displayed exponentials in (118), after suppressing the quadratic
remainder, are represented by

`exp(Y(t)) * exp(-Y(0)) * exp(t K)`.

Here `K` is the already constructed transported coarse variation.  The
curve is exactly the identity at `t = 0`.  Its derivative therefore fixes
the frame of the printed linear coordinate without identifying the full
nonlinear coarse Wilson curve with its first-order exponential model.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq118SourceMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The four-factor padding of the three exponentials displayed in (118). -/
def cmp98Eq118SourceFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![fun t => cmp98UbarExpAverage U b
      (t • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A)),
    fun _ => NormedSpace.exp (-(cmp98UbarLogAverage U b 0)),
    fun t => NormedSpace.exp
      (t • cmp98Eq119DirectCoarseTransportedVariation U A b),
    fun _ => 1]

/-- First variations of the four source factors at the background. -/
def cmp98Eq118SourceFactorVariations
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![fun _ => fderiv ℝ
      (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ)
      (cmp98UbarLogAverage U b 0)
      (cmp98UbarLogAveragePhysicalVariation U A b),
    fun _ => 0,
    fun _ => cmp98Eq119DirectCoarseTransportedVariation U A b,
    fun _ => 0]

@[simp] theorem cmp98Eq118SourceFactors_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactors U A b 0 t = cmp98UbarExpAverage U b
      (t • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A)) := rfl

@[simp] theorem cmp98Eq118SourceFactors_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactors U A b 1 t =
      NormedSpace.exp (-(cmp98UbarLogAverage U b 0)) := rfl

@[simp] theorem cmp98Eq118SourceFactors_two
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactors U A b 2 t = NormedSpace.exp
      (t • cmp98Eq119DirectCoarseTransportedVariation U A b) := rfl

@[simp] theorem cmp98Eq118SourceFactors_three
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactors U A b 3 t = 1 := rfl

@[simp] theorem cmp98Eq118SourceFactorVariations_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactorVariations U A b 0 t = fderiv ℝ
      (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ)
      (cmp98UbarLogAverage U b 0)
      (cmp98UbarLogAveragePhysicalVariation U A b) := rfl

@[simp] theorem cmp98Eq118SourceFactorVariations_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactorVariations U A b 1 t = 0 := rfl

@[simp] theorem cmp98Eq118SourceFactorVariations_two
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactorVariations U A b 2 t =
      cmp98Eq119DirectCoarseTransportedVariation U A b := rfl

@[simp] theorem cmp98Eq118SourceFactorVariations_three
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq118SourceFactorVariations U A b 3 t = 0 := rfl

/-- The exact first-order source curve extracted from (118). -/
def cmp98Eq118SourceCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  fourFactorProduct (cmp98Eq118SourceFactors U A b) t

/-- Every source factor has the stated derivative at zero. -/
theorem hasDerivAt_cmp98Eq118SourceFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (i : Fin 4) :
    HasDerivAt (cmp98Eq118SourceFactors U A b i)
      (cmp98Eq118SourceFactorVariations U A b i 0) 0 := by
  fin_cases i
  · exact hasDerivAt_cmp98UbarExpAverage_physicalLine U A b hsmall
  · simpa only [cmp98Eq118SourceFactors,
        cmp98Eq118SourceFactorVariations, Matrix.cons_val_one] using
      (hasDerivAt_const (x := (0 : ℝ))
        (c := NormedSpace.exp (-(cmp98UbarLogAverage U b 0))))
  · have hline : HasDerivAt
        (fun t : ℝ => t • cmp98Eq119DirectCoarseTransportedVariation U A b)
        (cmp98Eq119DirectCoarseTransportedVariation U A b) 0 := by
      have hraw := (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (cmp98Eq119DirectCoarseTransportedVariation U A b)
      change HasDerivAt
        (fun t : ℝ => t • cmp98Eq119DirectCoarseTransportedVariation U A b)
        ((1 : ℝ) • cmp98Eq119DirectCoarseTransportedVariation U A b) 0 at hraw
      have hone : (1 : ℝ) •
        cmp98Eq119DirectCoarseTransportedVariation U A b =
            cmp98Eq119DirectCoarseTransportedVariation U A b := by
        ext i j
        simp
      rw [hone] at hraw
      exact hraw
    have hexp0 : HasFDerivAt
        (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
          Matrix (Fin Nc) (Fin Nc) ℂ)
        (1 : Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ]
          Matrix (Fin Nc) (Fin Nc) ℂ)
        ((0 : ℝ) • cmp98Eq119DirectCoarseTransportedVariation U A b) := by
      have hzeroK : (0 : ℝ) •
          cmp98Eq119DirectCoarseTransportedVariation U A b = 0 :=
        zero_smul ℝ _
      rw [hzeroK]
      exact hasFDerivAt_exp_zero (𝕂 := ℝ)
        (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
    have hexp := hexp0.comp_hasDerivAt 0 hline
    simpa only [cmp98Eq118SourceFactors,
      cmp98Eq118SourceFactorVariations, Matrix.cons_val_two] using hexp
  · simpa only [cmp98Eq118SourceFactors,
        cmp98Eq118SourceFactorVariations, Matrix.cons_val_three] using
      (hasDerivAt_const (x := (0 : ℝ))
        (c := (1 : Matrix (Fin Nc) (Fin Nc) ℂ)))

/-- Structural product-rule derivative of the source curve. -/
theorem hasDerivAt_cmp98Eq118SourceCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    HasDerivAt (cmp98Eq118SourceCurve U A b)
      (fourFactorFirst (cmp98Eq118SourceFactors U A b)
        (cmp98Eq118SourceFactorVariations U A b) 0) 0 := by
  exact hasDerivAt_fourFactorProduct
    (cmp98Eq118SourceFactors U A b)
    (cmp98Eq118SourceFactorVariations U A b) 0
    (hasDerivAt_cmp98Eq118SourceFactors U A b hsmall)

/-- The source curve is based exactly at the identity. -/
theorem cmp98Eq118SourceCurve_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq118SourceCurve U A b 0 = 1 := by
  simp only [cmp98Eq118SourceCurve, fourFactorProduct,
    cmp98Eq118SourceFactors_zero, cmp98Eq118SourceFactors_one,
    cmp98Eq118SourceFactors_two, cmp98Eq118SourceFactors_three]
  have hzero : (0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A) = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  rw [hzero]
  have hzeroK : (0 : ℝ) •
      cmp98Eq119DirectCoarseTransportedVariation U A b = 0 := zero_smul ℝ _
  rw [hzeroK]
  simp only [cmp98UbarExpAverage, NormedSpace.exp_zero,
    mul_one, cmp98_exp_mul_exp_neg]

/-- The structural derivative is the two terms displayed in (118). -/
theorem cmp98Eq118SourceFirstVariation_eq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    fourFactorFirst (cmp98Eq118SourceFactors U A b)
        (cmp98Eq118SourceFactorVariations U A b) 0 =
      fderiv ℝ
          (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
            Matrix (Fin Nc) (Fin Nc) ℂ)
          (cmp98UbarLogAverage U b 0)
          (cmp98UbarLogAveragePhysicalVariation U A b) *
          NormedSpace.exp (-(cmp98UbarLogAverage U b 0)) +
        cmp98Eq119DirectCoarseTransportedVariation U A b := by
  simp only [fourFactorFirst, cmp98Eq118SourceFactors_zero,
    cmp98Eq118SourceFactors_one, cmp98Eq118SourceFactors_two,
    cmp98Eq118SourceFactors_three,
    cmp98Eq118SourceFactorVariations_zero,
    cmp98Eq118SourceFactorVariations_one,
    cmp98Eq118SourceFactorVariations_two,
    cmp98Eq118SourceFactorVariations_three]
  have hzero : (0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A) = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  rw [hzero]
  have hzeroK : (0 : ℝ) •
      cmp98Eq119DirectCoarseTransportedVariation U A b = 0 := zero_smul ℝ _
  rw [hzeroK]
  simp only [cmp98UbarExpAverage, NormedSpace.exp_zero,
    mul_one, mul_zero, add_zero, cmp98_exp_mul_exp_neg, one_mul]

/-- **Exact source-frame derivative of CMP98 (118).** -/
theorem deriv_cmp98Eq118SourceCurve_zero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    deriv (cmp98Eq118SourceCurve U A b) 0 =
      cmp98GAd (-(cmp98UbarLogAverage U b 0))
          (cmp98UbarLogAveragePhysicalVariation U A b) +
        cmp98Eq119DirectCoarseTransportedVariation U A b := by
  rw [(hasDerivAt_cmp98Eq118SourceCurve U A b hsmall).deriv,
    cmp98Eq118SourceFirstVariation_eq]
  exact congrArg
    (fun z => z + cmp98Eq119DirectCoarseTransportedVariation U A b)
    (cmp98_fderiv_exp_mul_exp_neg_eq_gad_neg_apply
      (cmp98UbarLogAverage U b 0)
      (cmp98UbarLogAveragePhysicalVariation U A b))

/-- The source-faithful first-order curve and the physical nonlinear proxy
have exactly the same right variation at the background. -/
theorem deriv_cmp98Eq118SourceCurve_zero_eq_nonlinearRightVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    deriv (cmp98Eq118SourceCurve U A b) 0 =
      cmp98Eq119NonlinearRightVariation U A b := by
  rw [deriv_cmp98Eq118SourceCurve_zero U A b hsmall,
    cmp98Eq119NonlinearRightVariation_eq U A b hsmall]

end

end YangMills.RG
