/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ContourFirstVariation
import YangMills.RG.BalabanCMP116FourFactorSecondDerivative

/-!
# Exact four-contour variation in the CMP98 block average

This file expands the derivative of the literal local deviation in CMP98
(121)--(124).  The first three factors are the source contours through the
fine point and the fourth is the conjugate transpose of the coarse straight
transport.  The derivative is therefore the ordered four-factor product
rule, including the differentiated adjoint fourth factor.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The four literal contour factors in the local CMP98 deviation. -/
def cmp98UbarContourFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![cmp98ContourMatrixCurve U A
      (cmp99SourceUbarGamma1 (G := SUN Nc) b x),
    cmp98ContourMatrixCurve U A
      (cmp99SourceUbarGamma2 (G := SUN Nc) b x),
    cmp98ContourMatrixCurve U A
      (cmp99SourceUbarGamma3 (G := SUN Nc) b x),
    fun t => (cmp98ContourMatrixCurve U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b) t)ᴴ]

/-- First variations of the four literal factors. -/
def cmp98UbarContourFactorVariations
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Fin 4 → ℝ → Matrix (Fin Nc) (Fin Nc) ℂ :=
  ![cmp98ContourFirstVariation U A
      (cmp99SourceUbarGamma1 (G := SUN Nc) b x),
    cmp98ContourFirstVariation U A
      (cmp99SourceUbarGamma2 (G := SUN Nc) b x),
    cmp98ContourFirstVariation U A
      (cmp99SourceUbarGamma3 (G := SUN Nc) b x),
    fun t => (cmp98ContourFirstVariation U A
      (cmp98SourceCoarseBondPath (Nc := Nc) b) t)ᴴ]

/-- Every literal factor has the claimed derivative, including the adjoint
coarse factor. -/
theorem hasDerivAt_cmp98UbarContourFactors
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (i : Fin 4) (t : ℝ) :
    HasDerivAt (cmp98UbarContourFactors U A b x i)
      (cmp98UbarContourFactorVariations U A b x i t) t := by
  fin_cases i
  · exact hasDerivAt_cmp98ContourMatrixCurve U A
      (cmp99SourceUbarGamma1 (G := SUN Nc) b x) t
  · exact hasDerivAt_cmp98ContourMatrixCurve U A
      (cmp99SourceUbarGamma2 (G := SUN Nc) b x) t
  · exact hasDerivAt_cmp98ContourMatrixCurve U A
      (cmp99SourceUbarGamma3 (G := SUN Nc) b x) t
  · simpa only [cmp98UbarContourFactors,
        cmp98UbarContourFactorVariations, Matrix.cons_val_three,
        matrixConjTransposeCLM_apply] using
      (matrixConjTransposeCLM (Nc := Nc)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) t)

/-- The physical one-parameter local deviation. -/
def cmp98UbarDeviationCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  fourFactorProduct (cmp98UbarContourFactors U A b x) t - 1

/-- The complete ordered first variation of the local deviation. -/
def cmp98UbarDeviationFirstVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  fourFactorFirst (cmp98UbarContourFactors U A b x)
    (cmp98UbarContourFactorVariations U A b x) t

/-- Exact derivative of the four-contour local deviation. -/
theorem hasDerivAt_cmp98UbarDeviationCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ) :
    HasDerivAt (cmp98UbarDeviationCurve U A b x)
      (cmp98UbarDeviationFirstVariation U A b x t) t := by
  simpa only [cmp98UbarDeviationCurve, cmp98UbarDeviationFirstVariation] using
    (hasDerivAt_fourFactorProduct
      (cmp98UbarContourFactors U A b x)
      (cmp98UbarContourFactorVariations U A b x) t
      (hasDerivAt_cmp98UbarContourFactors U A b x · t)).sub_const 1

/-- The physical deviation curve is literally the ambient CMP98 deviation
restricted to the physical tangent line. -/
theorem cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ) :
    cmp98UbarAmbientDeviationMatrix U b x
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      cmp98UbarDeviationCurve U A b x t := by
  simp [cmp98UbarAmbientDeviationMatrix, cmp98UbarDeviationCurve,
    cmp98UbarContourFactors, fourFactorProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  rw [cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve,
    cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve,
    cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve,
    cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve]

set_option maxHeartbeats 800000 in
/-- The ambient Fréchet derivative of the literal deviation, on a physical
one-cochain, is the complete four-contour ordered variation. -/
theorem fderiv_cmp98UbarAmbientDeviationMatrix_zero_apply_physical
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    fderiv ℝ (fun Z => cmp98UbarAmbientDeviationMatrix U b x Z) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      cmp98UbarDeviationFirstVariation U A b x 0 := by
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have hline : HasDerivAt (fun t : ℝ => t • V) V 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const V
  have hout : HasFDerivAt
      (fun Z => cmp98UbarAmbientDeviationMatrix U b x Z)
      (fderiv ℝ (fun Z => cmp98UbarAmbientDeviationMatrix U b x Z)
        ((0 : ℝ) • V)) ((0 : ℝ) • V) :=
    (analyticAt_cmp98UbarAmbientDeviationMatrix U b x ((0 : ℝ) • V))
      |>.differentiableAt.hasFDerivAt
  have hambient : HasDerivAt
      (fun t : ℝ => cmp98UbarAmbientDeviationMatrix U b x (t • V))
      (fderiv ℝ (fun Z => cmp98UbarAmbientDeviationMatrix U b x Z) 0 V) 0 := by
    have hcomp := hout.comp_hasDerivAt 0 hline
    have hzero : (0 : ℝ) • V = 0 := zero_smul ℝ V
    rw [hzero] at hcomp
    simpa [Function.comp_def] using hcomp
  have hphysical : HasDerivAt
      (fun t : ℝ => cmp98UbarAmbientDeviationMatrix U b x (t • V))
      (cmp98UbarDeviationFirstVariation U A b x 0) 0 := by
    convert hasDerivAt_cmp98UbarDeviationCurve U A b x 0 using 1
    funext t
    simpa [V] using
      (cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve U A b x t)
  exact hambient.unique hphysical

end

end YangMills.RG
