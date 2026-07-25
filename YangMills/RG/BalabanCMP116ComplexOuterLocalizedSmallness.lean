/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexOuterLocalizedEnergy
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm

/-!
# Dimension-free smallness for the combined CMP116 outer quadratic

The complex `R₁` quadratic and the localized source energy must be integrated
together.  This module derives both the shifted positivity and the matrix
radius required by that integral from the same bilateral `L∞` budget.  No
ambient coordinate cardinality is introduced.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

/-- Complexifying the symmetric entrywise-real part costs at most the
bilateral row/column budget of the original complex matrix. -/
theorem norm_complexified_symmetricRealPart_le_bilateral
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    ‖(cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
        Complex.ofRealHom‖ ≤
      (‖A‖ + ‖A.transpose‖) / 2 := by
  apply Matrix.linfty_opNorm_le_of_row_sum_le
  · positivity
  · intro i
    calc
      ∑ j,
          ‖((cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
              Complex.ofRealHom) i j‖ =
          ∑ j, |(1 / 2 : ℝ) *
            ((A i j).re + (A j i).re)| := by
              apply Finset.sum_congr rfl
              intro j _
              simp only [Matrix.map_apply, Complex.norm_real]
              congr 1
              simp [cmp116Eq214ComplexQuadraticSymmetricRealPart,
                cmp116Eq214RealPartMatrix]
              rw [← Complex.ofReal_add]
              exact Complex.norm_real _
      _ ≤ ∑ j, (1 / 2 : ℝ) * (‖A i j‖ + ‖A j i‖) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          |(1 / 2 : ℝ) * ((A i j).re + (A j i).re)| =
              (1 / 2 : ℝ) * |(A i j).re + (A j i).re| := by
            rw [abs_mul]
            norm_num
          _ ≤ (1 / 2 : ℝ) *
              (|(A i j).re| + |(A j i).re|) := by
            exact mul_le_mul_of_nonneg_left
              (abs_add_le _ _) (by norm_num)
          _ ≤ (1 / 2 : ℝ) * (‖A i j‖ + ‖A j i‖) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add (Complex.abs_re_le_norm _)
                (Complex.abs_re_le_norm _)) (by norm_num)
      _ = (1 / 2 : ℝ) *
          ((∑ j, ‖A i j‖) + ∑ j, ‖A.transpose i j‖) := by
        simp only [Matrix.transpose_apply]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖A.transpose‖) := by
        gcongr
        · exact Matrix.row_sum_norm_le_linfty_opNorm A i
        · exact Matrix.row_sum_norm_le_linfty_opNorm A.transpose i
      _ = (‖A‖ + ‖A.transpose‖) / 2 := by ring

/-- The localized source energy adds exactly `2 * |beta|` to the bilateral
matrix radius, independently of the number of ambient Gaussian coordinates. -/
theorem norm_complexified_neg_symmetricRealPart_add_localizedEnergy_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (S : Finset ι) (beta : ℝ) :
    ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
        (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).map
          Complex.ofRealHom‖ ≤
      (‖A‖ + ‖A.transpose‖) / 2 + 2 * |beta| := by
  have hsplit :
      cmp116Eq214ComplexQuadraticSymmetricRealPart
          (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta) =
        cmp116Eq214ComplexQuadraticSymmetricRealPart A +
          (2 * beta) • cmp116Eq223CoordinateProjection S := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ S <;>
        simp [cmp116Eq214ComplexQuadraticSymmetricRealPart,
          cmp116Eq214RealPartMatrix,
          cmp116Eq214LocalizedOuterEnergyMatrix,
          cmp116Eq223CoordinateProjection, Matrix.diagonal, hi]
      <;> ring
    · simp [cmp116Eq214ComplexQuadraticSymmetricRealPart,
        cmp116Eq214RealPartMatrix,
        cmp116Eq214LocalizedOuterEnergyMatrix,
        cmp116Eq223CoordinateProjection, Matrix.diagonal, hij,
        Ne.symm hij]
  rw [hsplit]
  have hmap :
      (-(cmp116Eq214ComplexQuadraticSymmetricRealPart A +
          (2 * beta) • cmp116Eq223CoordinateProjection S)).map
          Complex.ofRealHom =
        -((cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
            Complex.ofRealHom +
          ((2 * beta) • cmp116Eq223CoordinateProjection S).map
            Complex.ofRealHom) := by
    ext i j
    simp
  rw [hmap, norm_neg]
  calc
    ‖(cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
          Complex.ofRealHom +
        ((2 * beta) • cmp116Eq223CoordinateProjection S).map
          Complex.ofRealHom‖ ≤
        ‖(cmp116Eq214ComplexQuadraticSymmetricRealPart A).map
          Complex.ofRealHom‖ +
        ‖((2 * beta) • cmp116Eq223CoordinateProjection S).map
          Complex.ofRealHom‖ := norm_add_le _ _
    _ ≤ (‖A‖ + ‖A.transpose‖) / 2 + 2 * |beta| := by
      apply add_le_add
      · exact norm_complexified_symmetricRealPart_le_bilateral A
      · apply Matrix.linfty_opNorm_le_of_row_sum_le
        · positivity
        · intro i
          rw [Finset.sum_eq_single i]
          · by_cases hi : i ∈ S
            · simp [cmp116Eq223CoordinateProjection, Matrix.diagonal, hi]
            · simp [cmp116Eq223CoordinateProjection, Matrix.diagonal, hi]
          · intro j _ hji
            simp [cmp116Eq223CoordinateProjection, Matrix.diagonal,
              Ne.symm hji]
          · simp

/-- The same dimension-free bilateral radius gives strict positivity of the
shifted standard-Gaussian precision.  The factor `2` is forced by the
`1 / 2` in `cmp116Eq214ComplexQuadratic`. -/
theorem posDef_one_sub_symmetricRealPart_add_localizedEnergy_of_bilateral_small
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (S : Finset ι) (beta : ℝ)
    (hsmall : (‖A‖ + ‖A.transpose‖) / 2 + 2 * |beta| < 1) :
    (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart
      (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).PosDef := by
  let H := cmp116Eq214ComplexQuadraticSymmetricRealPart
    (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_one.sub
      (by
        change Matrix.transpose H = H
        simpa [H] using
          cmp116Eq214ComplexQuadraticSymmetricRealPart_transpose
            (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta))
  · intro x hx
    have hxpos : 0 < x ⬝ᵥ x := by
      simpa using Matrix.PosDef.one.dotProduct_mulVec_pos hx
    have hquad :
        dotProduct x (H.mulVec x) ≤
          ((‖A‖ + ‖A.transpose‖) / 2 + 2 * |beta|) *
            dotProduct x x := by
      have hA :=
        cmp116Eq214ComplexQuadratic_re_le_linfty_bilateral A x
      have hS :
          beta * ∑ i ∈ S, x i ^ 2 ≤
            |beta| * ∑ i, x i ^ 2 := by
        calc
          beta * ∑ i ∈ S, x i ^ 2 ≤
              |beta| * ∑ i ∈ S, x i ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (le_abs_self beta) (Finset.sum_nonneg fun i _ => sq_nonneg _)
          _ ≤ |beta| * ∑ i, x i ^ 2 := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_univ S) (fun _ _ _ => sq_nonneg _))
              (abs_nonneg beta)
      have hcombined :
          (cmp116Eq214ComplexQuadratic
            (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta) x).re ≤
              ((‖A‖ + ‖A.transpose‖) / 4 + |beta|) *
                ∑ i, x i ^ 2 := by
        rw [cmp116Eq214ComplexQuadratic_add_localizedOuterEnergyMatrix,
          Complex.add_re, Complex.ofReal_re]
        linarith
      rw [cmp116Eq214ComplexQuadratic_re_eq_symmetricRealPart] at hcombined
      have hdouble :
          dotProduct x (H.mulVec x) ≤
              2 * (((‖A‖ + ‖A.transpose‖) / 4 + |beta|) *
                ∑ i, x i ^ 2) := by
        simpa [H] using (show
          dotProduct x
              ((cmp116Eq214ComplexQuadraticSymmetricRealPart
                (A + cmp116Eq214LocalizedOuterEnergyMatrix S beta)).mulVec x) ≤
              2 * (((‖A‖ + ‖A.transpose‖) / 4 + |beta|) *
                ∑ i, x i ^ 2) by
          linarith)
      calc
        dotProduct x (H.mulVec x) ≤
            2 * (((‖A‖ + ‖A.transpose‖) / 4 + |beta|) *
              ∑ i, x i ^ 2) := hdouble
        _ = ((‖A‖ + ‖A.transpose‖) / 2 + 2 * |beta|) *
            dotProduct x x := by
          simp only [dotProduct, pow_two]
          ring
    have hstrict :
        dotProduct x (H.mulVec x) < dotProduct x x := by
      calc
        dotProduct x (H.mulVec x) ≤
            ((‖A‖ + ‖A.transpose‖) / 2 + 2 * |beta|) *
              dotProduct x x := hquad
        _ < 1 * dotProduct x x :=
          mul_lt_mul_of_pos_right hsmall hxpos
        _ = dotProduct x x := one_mul _
    change 0 < dotProduct x ((1 - H).mulVec x)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    exact sub_pos.mpr hstrict

end

end YangMills.RG
