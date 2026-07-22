/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98SourceGAdSmallField
import YangMills.RG.BalabanCMP98OrderedContourTransport

/-!
# Right-trivialized four-contour algebra behind CMP98 (124)

Before matching the three printed correction lines, the derivative of the
four literal contour factors must be transported to one common basepoint.
This module proves that noncommutative identity exactly.  It does not yet
identify the four prefix-transported pieces with the source symbols in
(124); that dictionary remains a separate, auditable step.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

omit [NeZero Nc] in
theorem mul_conjTranspose_mul_cancel_right
    (a x : Matrix (Fin Nc) (Fin Nc) ℂ)
    (ha : a * Matrix.conjTranspose a = 1) :
    a * (Matrix.conjTranspose a * x) = x := by
  rw [← mul_assoc, ha, one_mul]

/- Algebraic four-factor product rule after right trivialization.  Every
factor is allowed to be noncommutative; only its exact unitary identity is
used to cancel the suffix to its right. -/
omit [NeZero Nc] in
theorem fourFactorFirst_mul_conjTranspose_eq_prefixRightVariations
    (a b c e da db dc de : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hb : b * Matrix.conjTranspose b = 1)
    (hc : c * Matrix.conjTranspose c = 1)
    (he : e * Matrix.conjTranspose e = 1) :
    (((((da * b + a * db) * c + (a * b) * dc) * e) +
          ((a * b) * c) * de) *
        Matrix.conjTranspose (((a * b) * c) * e)) =
      da * Matrix.conjTranspose a +
        a * (db * Matrix.conjTranspose b) * Matrix.conjTranspose a +
        (a * b) * (dc * Matrix.conjTranspose c) *
          Matrix.conjTranspose (a * b) +
        ((a * b) * c) * (de * Matrix.conjTranspose e) *
          Matrix.conjTranspose ((a * b) * c) := by
  simp only [Matrix.conjTranspose_mul, add_mul, mul_assoc,
    mul_conjTranspose_mul_cancel_right e _ he,
    mul_conjTranspose_mul_cancel_right c _ hc,
    mul_conjTranspose_mul_cancel_right b _ hb]

/-- At zero tangent, every contour matrix curve is the defining matrix of
the corresponding physical `SU(N)` Wilson line, for arbitrary orientations. -/
theorem cmp98ContourMatrixCurve_zero_eq_wilsonLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    cmp98ContourMatrixCurve U A es 0 = (wilsonLine U es : SUN Nc).val := by
  have h := cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve U A es 0
  have hzero : (0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A) = 0 := zero_smul _ _
  rw [hzero, cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine] at h
  exact h.symm

/-- Arbitrarily oriented physical contour matrices remain exactly unitary
at the background point. -/
theorem cmp98ContourMatrixCurve_zero_mul_conjTranspose_general
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    cmp98ContourMatrixCurve U A es 0 *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A es 0) = 1 := by
  rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine]
  exact su_mul_conjTranspose_self (wilsonLine U es : SUN Nc)

/-- The complete physical contour curve stays unitary at every real chart
parameter.  This is stronger than the background-point cancellation above
and is the identity whose derivative fixes the sign of the inverse contour
in CMP98 (124). -/
theorem cmp98ContourMatrixCurve_mul_conjTranspose_general
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    cmp98ContourMatrixCurve U A es t *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t) = 1 := by
  let X : PhysicalSuMatrixTangent d (M * N') Nc :=
    physicalCochainToSuMatrixTangent A
  have htangent :
      physicalTwoParameterAmbientTangent X 0 t 0 =
        t • physicalSuTangentToAmbient X := by
    funext b
    change t • (X b).toMatrix +
      (0 : ℝ) • ((0 : PhysicalSuMatrixTangent d (M * N') Nc) b).toMatrix =
        t • (X b).toMatrix
    have hz : (0 : ℝ) •
        ((0 : PhysicalSuMatrixTangent d (M * N') Nc) b).toMatrix = 0 :=
      zero_smul ℝ _
    rw [hz, add_zero]
  have hcurve :
      cmp98ContourMatrixCurve U A es t =
        (wilsonLine (physicalSuUnitaryLeftVariation U X 0 t 0) es : UN Nc).val := by
    rw [← cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve U A es t,
      ← htangent]
    exact cmp98AmbientWilsonLineMatrix_twoParameter_eq_unitaryWilsonLine
      U X 0 t 0 es
  rw [hcurve]
  exact Unitary.coe_mul_star_self
    (wilsonLine (physicalSuUnitaryLeftVariation U X 0 t 0) es : UN Nc)

/-- The opposite unitary cancellation, retained separately because its
derivative is the form used by the inverse fourth contour. -/
theorem cmp98ContourMatrixCurve_conjTranspose_mul_general
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t) *
        cmp98ContourMatrixCurve U A es t = 1 := by
  let X : PhysicalSuMatrixTangent d (M * N') Nc :=
    physicalCochainToSuMatrixTangent A
  have htangent :
      physicalTwoParameterAmbientTangent X 0 t 0 =
        t • physicalSuTangentToAmbient X := by
    funext b
    change t • (X b).toMatrix +
      (0 : ℝ) • ((0 : PhysicalSuMatrixTangent d (M * N') Nc) b).toMatrix =
        t • (X b).toMatrix
    have hz : (0 : ℝ) •
        ((0 : PhysicalSuMatrixTangent d (M * N') Nc) b).toMatrix = 0 :=
      zero_smul ℝ _
    rw [hz, add_zero]
  have hcurve :
      cmp98ContourMatrixCurve U A es t =
        (wilsonLine (physicalSuUnitaryLeftVariation U X 0 t 0) es : UN Nc).val := by
    rw [← cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve U A es t,
      ← htangent]
    exact cmp98AmbientWilsonLineMatrix_twoParameter_eq_unitaryWilsonLine
      U X 0 t 0 es
  rw [hcurve]
  exact Unitary.coe_star_mul_self
    (wilsonLine (physicalSuUnitaryLeftVariation U X 0 t 0) es : UN Nc)

/-- Differentiating contour unitarity gives the exact tangent relation used
for the conjugate-transposed fourth factor. -/
theorem cmp98ContourFirstVariation_mul_conjTranspose_add
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    cmp98ContourFirstVariation U A es 0 *
          Matrix.conjTranspose (cmp98ContourMatrixCurve U A es 0) +
        cmp98ContourMatrixCurve U A es 0 *
          Matrix.conjTranspose (cmp98ContourFirstVariation U A es 0) = 0 := by
  have hcurve := hasDerivAt_cmp98ContourMatrixCurve U A es 0
  have hstar : HasDerivAt
      (fun t => Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t))
      (Matrix.conjTranspose (cmp98ContourFirstVariation U A es 0)) 0 := by
    simpa only [matrixConjTransposeCLM_apply] using
      (matrixConjTransposeCLM (Nc := Nc)).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hprod := hcurve.mul hstar
  change HasDerivAt
    (fun t => cmp98ContourMatrixCurve U A es t *
      Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t)) _ 0 at hprod
  have hconst :
      (fun t : ℝ => cmp98ContourMatrixCurve U A es t *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t)) =
      fun _ => (1 : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    funext t
    exact cmp98ContourMatrixCurve_mul_conjTranspose_general U A es t
  rw [hconst] at hprod
  exact hprod.unique (hasDerivAt_const (x := (0 : ℝ))
    (c := (1 : Matrix (Fin Nc) (Fin Nc) ℂ)))

/-- Right-trivialized derivative of the inverse contour is the negative of
the left-trivialized derivative of the original contour. -/
theorem cmp98ConjTransposeFirstVariation_mul_contour
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    Matrix.conjTranspose (cmp98ContourFirstVariation U A es 0) *
        cmp98ContourMatrixCurve U A es 0 =
      -(Matrix.conjTranspose (cmp98ContourMatrixCurve U A es 0) *
        cmp98ContourFirstVariation U A es 0) := by
  have hcurve := hasDerivAt_cmp98ContourMatrixCurve U A es 0
  have hstar : HasDerivAt
      (fun t => Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t))
      (Matrix.conjTranspose (cmp98ContourFirstVariation U A es 0)) 0 := by
    simpa only [matrixConjTransposeCLM_apply] using
      (matrixConjTransposeCLM (Nc := Nc)).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hprod := hstar.mul hcurve
  change HasDerivAt
    (fun t => Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t) *
      cmp98ContourMatrixCurve U A es t) _ 0 at hprod
  have hconst :
      (fun t : ℝ => Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t) *
        cmp98ContourMatrixCurve U A es t) =
      fun _ => (1 : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    funext t
    exact cmp98ContourMatrixCurve_conjTranspose_mul_general U A es t
  rw [hconst] at hprod
  have hzero := hprod.unique (hasDerivAt_const (x := (0 : ℝ))
    (c := (1 : Matrix (Fin Nc) (Fin Nc) ℂ)))
  exact (add_eq_zero_iff_eq_neg.mp hzero)

/-- Source specialization for the fourth factor of the CMP98 deviation.
Its right variation is exactly the negative coarse-contour left variation;
the sign is derived from physical unitarity rather than stipulated. -/
theorem cmp98CoarseInverseFactor_rightVariation_eq_neg_leftVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    cmp98UbarContourFactorVariations U A b x 3 0 *
        Matrix.conjTranspose (cmp98UbarContourFactors U A b x 3 0) =
      -(Matrix.conjTranspose (cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) *
        cmp98ContourFirstVariation U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) := by
  change Matrix.conjTranspose (cmp98ContourFirstVariation U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) *
      Matrix.conjTranspose (Matrix.conjTranspose (cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)) = _
  rw [Matrix.conjTranspose_conjTranspose]
  exact cmp98ConjTransposeFirstVariation_mul_contour U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b)

/-- The fourth, conjugate-transposed coarse factor is likewise unitary. -/
theorem cmp98CoarseConjTransposeFactor_zero_mul_conjTranspose
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    Matrix.conjTranspose (cmp98ContourMatrixCurve U A
          (cmp98SourceCoarseBondPath (Nc := Nc) b) 0) *
        Matrix.conjTranspose (Matrix.conjTranspose
          (cmp98ContourMatrixCurve U A
            (cmp98SourceCoarseBondPath (Nc := Nc) b) 0)) = 1 := by
  rw [Matrix.conjTranspose_conjTranspose]
  rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine]
  exact su_conjTranspose_mul_self (wilsonLine U
    (cmp98SourceCoarseBondPath (Nc := Nc) b) : SUN Nc)

/-- The zero-tangent product of the four analytic factors is the defining
matrix of the literal physical CMP99 deviation group element. -/
theorem cmp98UbarFourFactorProduct_zero_eq_sourceDeviation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    fourFactorProduct (cmp98UbarContourFactors U A b x) 0 =
      ((MatrixRealization.rep
        (UbarDeviation U (cmp99SourceBaseCoarseBackground U)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)) :
            Units (Matrix (Fin Nc) (Fin Nc) ℂ)).val) := by
  have h :=
    cmp98UbarAmbientDeviationMatrix_zero_eq_sourceUbarDeviationLogArg U b x
  unfold cmp98UbarAmbientDeviationMatrix UbarDeviationLogArg at h
  rw [cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    ← cmp98ContourMatrixCurve_zero_eq_wilsonLine U A,
    cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    ← cmp98ContourMatrixCurve_zero_eq_wilsonLine U A,
    cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    ← cmp98ContourMatrixCurve_zero_eq_wilsonLine U A,
    cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine,
    ← cmp98ContourMatrixCurve_zero_eq_wilsonLine U A] at h
  change fourFactorProduct (cmp98UbarContourFactors U A b x) 0 - 1 =
    _ - 1 at h
  calc
    _ = fourFactorProduct (cmp98UbarContourFactors U A b x) 0 - 1 + 1 := by
      abel
    _ = _ - 1 + 1 := congrArg (fun Z => Z + 1) h
    _ = _ := by abel

/-- The complete four-factor product has the second unitary cancellation
needed to convert right-trivialized contour pieces back to the left
trivialization consumed by the logarithmic derivative. -/
theorem cmp98UbarFourFactorProduct_zero_conjTranspose_mul
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix.conjTranspose
        (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) *
      fourFactorProduct (cmp98UbarContourFactors U A b x) 0 = 1 := by
  rw [cmp98UbarFourFactorProduct_zero_eq_sourceDeviation]
  exact su_conjTranspose_mul_self
    (UbarDeviation U (cmp99SourceBaseCoarseBackground U)
      (positiveEdgeOfPhysicalBond b) x
      (cmp99SourceUbarGamma1 (G := SUN Nc) b)
      (cmp99SourceUbarGamma2 (G := SUN Nc) b)
      (cmp99SourceUbarGamma3 (G := SUN Nc) b))

/-- Exact conversion between left and right trivializations of the complete
four-contour derivative. -/
theorem cmp98Ubar_leftVariation_eq_conj_rightVariation_mul
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix.conjTranspose
        (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) *
      cmp98UbarDeviationFirstVariation U A b x 0 =
    Matrix.conjTranspose
        (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) *
      (cmp98UbarDeviationFirstVariation U A b x 0 *
        Matrix.conjTranspose
          (fourFactorProduct (cmp98UbarContourFactors U A b x) 0)) *
      fourFactorProduct (cmp98UbarContourFactors U A b x) 0 := by
  symm
  simp only [mul_assoc,
    cmp98UbarFourFactorProduct_zero_conjTranspose_mul, mul_one]

/-- **Exact physical prefix decomposition.**  Right trivialization of the
complete four-contour derivative is the sum of the four single-contour
right variations, each conjugated by the product of the preceding physical
contours.  This is the source-safe starting point for the final regrouping
in CMP98 (124). -/
theorem cmp98UbarDeviationFirstVariation_mul_conjTranspose_eq_prefixRightVariations
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    cmp98UbarDeviationFirstVariation U A b x 0 *
        Matrix.conjTranspose
          (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) =
      let a := cmp98UbarContourFactors U A b x 0 0
      let q := cmp98UbarContourFactors U A b x 1 0
      let r := cmp98UbarContourFactors U A b x 2 0
      let s := cmp98UbarContourFactors U A b x 3 0
      let da := cmp98UbarContourFactorVariations U A b x 0 0
      let dq := cmp98UbarContourFactorVariations U A b x 1 0
      let dr := cmp98UbarContourFactorVariations U A b x 2 0
      let ds := cmp98UbarContourFactorVariations U A b x 3 0
      da * Matrix.conjTranspose a +
        a * (dq * Matrix.conjTranspose q) * Matrix.conjTranspose a +
        (a * q) * (dr * Matrix.conjTranspose r) *
          Matrix.conjTranspose (a * q) +
        ((a * q) * r) * (ds * Matrix.conjTranspose s) *
          Matrix.conjTranspose ((a * q) * r) := by
  simp only [cmp98UbarDeviationFirstVariation, fourFactorFirst,
    fourFactorProduct]
  apply fourFactorFirst_mul_conjTranspose_eq_prefixRightVariations
  · exact cmp98ContourMatrixCurve_zero_mul_conjTranspose_general U A
      (cmp99SourceUbarGamma2 (G := SUN Nc) b x)
  · exact cmp98ContourMatrixCurve_zero_mul_conjTranspose_general U A
      (cmp99SourceUbarGamma3 (G := SUN Nc) b x)
  · exact cmp98CoarseConjTransposeFactor_zero_mul_conjTranspose U A b

end

end YangMills.RG
