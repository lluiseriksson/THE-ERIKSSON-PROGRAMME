/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq224DeterminantBound
import YangMills.RG.BalabanCMP116QuadraticGaussianMatrix
import YangMills.RG.BalabanCMP116Eq223CovarianceOpNorm

/-!
# CMP116 equation (2.24): completed-square source and full majorant bounds

The exact Gaussian majorant contains both an inverse-square-root determinant
and the completed-square source exponential.  The determinant factor is
bounded in `BalabanCMP116Eq224DeterminantBound`.  This module closes the
matching source estimate for the real positive Gaussian that dominates the
physical integrand.

For `B = I - Rᵀ (alpha P_Z0) R`, spectral diagonalization proves

`rᵀ B⁻¹ r <= ‖r‖² / (1 - alpha * ‖R‖²)`.

After the covariance-root transport of the source, the complete explicit
(2.24) majorant is bounded by

`sqrt((1-q)^n)⁻¹ * exp(‖R‖² * ‖r‖² / (2 * (1-q)))`,

where `q = alpha * ‖R‖² < 1`.

Honest scope: this removes the matrix inverse/determinant content of
`hmajorant` for the real dominating source.  Uniform source-specific bounds on
`‖r‖²`, the model-specific kernel inputs, the conversion to (2.26), `hraw`,
and `hRpoly` remain open.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

theorem map_mulVec_ofReal
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (y : ι → ℝ) :
    M.map Complex.ofRealHom *ᵥ (fun i => (y i : ℂ)) =
      fun i => ((M *ᵥ y) i : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem ofReal_dotProduct
    {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    ((x ⬝ᵥ y : ℝ) : ℂ) =
      (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (y i : ℂ)) := by
  simp [dotProduct]

theorem posDef_real_inverse_eq_spectral_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosDef) (y : ι → ℝ) :
    y ⬝ᵥ (B⁻¹ *ᵥ y) =
      ∑ i,
        ((star (hB.1.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ y) i) ^ 2 /
          hB.1.eigenvalues i := by
  have h := posDef_complex_bilinear_inverse_eq_spectral_sum
    B hB (fun i => (y i : ℂ))
  apply Complex.ofReal_injective
  rw [ofReal_dotProduct, ← map_mulVec_ofReal]
  rw [h]
  push_cast
  simp [map_mulVec_ofReal]

theorem eigenvalue_ge_of_posDef_quadratic_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosDef) (lower : ℝ)
    (hlower : ∀ x : ι → ℝ,
      lower * (x ⬝ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) (i : ι) :
    lower ≤ hB.1.eigenvalues i := by
  let v : ι → ℝ := ⇑(hB.1.eigenvectorBasis i)
  have h := hlower v
  have hvne : v ≠ 0 := by
    simpa [v] using hB.1.eigenvectorBasis.orthonormal.ne_zero i
  have hvpos : 0 < v ⬝ᵥ v := by
    have hnonneg : 0 ≤ v ⬝ᵥ v := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    have hne : v ⬝ᵥ v ≠ 0 := by
      intro hzero
      exact hvne (dotProduct_self_eq_zero.mp hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have heig : B *ᵥ v = (hB.1.eigenvalues i) • v :=
    hB.1.mulVec_eigenvectorBasis i
  rw [heig, dotProduct_smul] at h
  simp only [smul_eq_mul] at h
  nlinarith

theorem dotProduct_star_unitary_mulVec_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix.unitaryGroup ι ℝ) (y : ι → ℝ) :
    (star (Q : Matrix ι ι ℝ) *ᵥ y) ⬝ᵥ
        (star (Q : Matrix ι ι ℝ) *ᵥ y) = y ⬝ᵥ y := by
  let S : Matrix ι ι ℝ := star (Q : Matrix ι ι ℝ)
  have htranspose : Sᵀ = (Q : Matrix ι ι ℝ) := by
    ext i j
    simp [S, Matrix.transpose_apply]
  have hunit :
      (Q : Matrix ι ι ℝ) * star (Q : Matrix ι ι ℝ) = 1 :=
    Unitary.coe_mul_star_self Q
  change (S *ᵥ y) ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ y
  calc
    (S *ᵥ y) ⬝ᵥ (S *ᵥ y) =
        ((Q : Matrix ι ι ℝ) *ᵥ (S *ᵥ y)) ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec]
      rw [← Matrix.mulVec_transpose, htranspose]
    _ = y ⬝ᵥ y := by
      rw [Matrix.mulVec_mulVec]
      change (((Q : Matrix ι ι ℝ) * star (Q : Matrix ι ι ℝ)) *ᵥ y) ⬝ᵥ y = _
      rw [hunit, Matrix.one_mulVec]

theorem posDef_inverse_quadratic_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosDef) (lower : ℝ)
    (hlowerpos : 0 < lower)
    (hlower : ∀ x : ι → ℝ,
      lower * (x ⬝ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x))
    (y : ι → ℝ) :
    y ⬝ᵥ (B⁻¹ *ᵥ y) ≤ (y ⬝ᵥ y) / lower := by
  rw [posDef_real_inverse_eq_spectral_sum B hB y]
  let d : ι → ℝ :=
    star (hB.1.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ y
  calc
    (∑ i, d i ^ 2 / hB.1.eigenvalues i) ≤
        ∑ i, d i ^ 2 / lower := by
      apply Finset.sum_le_sum
      intro i hi
      have heigpos : 0 < hB.1.eigenvalues i := hB.eigenvalues_pos i
      have hle := eigenvalue_ge_of_posDef_quadratic_lower B hB lower hlower i
      exact div_le_div_of_nonneg_left (sq_nonneg (d i)) hlowerpos hle
    _ = (∑ i, d i ^ 2) / lower := by rw [Finset.sum_div]
    _ = (y ⬝ᵥ y) / lower := by
      have hdot := dotProduct_star_unitary_mulVec_self
        hB.1.eigenvectorUnitary y
      rw [dotProduct] at hdot
      simpa [d, pow_two] using congrArg (fun z : ℝ => z / lower) hdot

theorem quadratic_one_sub_localized_covariance_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha covarianceBound : ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ x : ι → ℝ,
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ covarianceBound * (x ⬝ᵥ x))
    (x : ι → ℝ) :
    (1 - alpha * covarianceBound) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ ((1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) *ᵥ x) := by
  have hupper := quadratic_localized_covariance_le
    S R alpha covarianceBound halpha hcov x
  rw [sub_mulVec, one_mulVec, dotProduct_sub]
  linarith

theorem inverse_quadratic_one_sub_localized_covariance_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha covarianceBound : ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ x : ι → ℝ,
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ covarianceBound * (x ⬝ᵥ x))
    (hsmall : alpha * covarianceBound < 1)
    (y : ι → ℝ) :
    y ⬝ᵥ ((1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R)⁻¹ *ᵥ y) ≤
      (y ⬝ᵥ y) / (1 - alpha * covarianceBound) := by
  let B : Matrix ι ι ℝ :=
    1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R
  have hB : B.PosDef := by
    exact posDef_one_sub_localized_covariance_of_small
      S R alpha covarianceBound halpha hcov hsmall
  exact posDef_inverse_quadratic_le B hB
    (1 - alpha * covarianceBound) (sub_pos.mpr hsmall)
    (quadratic_one_sub_localized_covariance_ge
      S R alpha covarianceBound halpha hcov) y

open scoped Matrix.Norms.L2Operator

theorem cmp116Eq224_localized_source_re_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (r : ι → ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖R‖ ^ 2 < 1) :
    let B : Matrix ι ι ℝ :=
      1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R
    let cR : ι → ℂ :=
      (Rᵀ.map Complex.ofRealHom) *ᵥ (fun i => (r i : ℂ))
    ((cR ⬝ᵥ ((B⁻¹).map Complex.ofRealHom *ᵥ cR)) / 2).re ≤
      (‖R‖ ^ 2 * (r ⬝ᵥ r)) / (2 * (1 - alpha * ‖R‖ ^ 2)) := by
  dsimp only
  let B : Matrix ι ι ℝ :=
    1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R
  let y : ι → ℝ := Rᵀ *ᵥ r
  have hcR :
      (Rᵀ.map Complex.ofRealHom) *ᵥ (fun i => (r i : ℂ)) =
        fun i => (y i : ℂ) := by
    exact map_mulVec_ofReal Rᵀ r
  have hBmap :
      (B⁻¹).map Complex.ofRealHom *ᵥ (fun i => (y i : ℂ)) =
        fun i => ((B⁻¹ *ᵥ y) i : ℂ) :=
    map_mulVec_ofReal B⁻¹ y
  have hre :
      ((((fun i => (y i : ℂ)) ⬝ᵥ
        ((B⁻¹).map Complex.ofRealHom *ᵥ (fun i => (y i : ℂ)))) / 2).re) =
        (y ⬝ᵥ (B⁻¹ *ᵥ y)) / 2 := by
    rw [hBmap, ← ofReal_dotProduct]
    norm_num
  rw [hcR, hre]
  have hinv :
      y ⬝ᵥ (B⁻¹ *ᵥ y) ≤ (y ⬝ᵥ y) / (1 - alpha * ‖R‖ ^ 2) := by
    exact inverse_quadratic_one_sub_localized_covariance_le
      S R alpha (‖R‖ ^ 2) halpha
      (dotProduct_mulVec_self_le_l2_opNorm_sq R) hsmall y
  have hy : y ⬝ᵥ y ≤ ‖R‖ ^ 2 * (r ⬝ᵥ r) := by
    have ht := dotProduct_mulVec_self_le_l2_opNorm_sq Rᵀ r
    have hnorm : ‖Rᵀ‖ = ‖R‖ := by
      simpa using (Matrix.l2_opNorm_conjTranspose R)
    rw [hnorm] at ht
    exact ht
  have hlower : 0 < 1 - alpha * ‖R‖ ^ 2 := sub_pos.mpr hsmall
  calc
    (y ⬝ᵥ (B⁻¹ *ᵥ y)) / 2 ≤
        ((y ⬝ᵥ y) / (1 - alpha * ‖R‖ ^ 2)) / 2 := by linarith
    _ ≤ ((‖R‖ ^ 2 * (r ⬝ᵥ r)) /
        (1 - alpha * ‖R‖ ^ 2)) / 2 := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hy hlower.le) (by norm_num)
    _ = (‖R‖ ^ 2 * (r ⬝ᵥ r)) /
        (2 * (1 - alpha * ‖R‖ ^ 2)) := by
      field_simp [ne_of_gt hlower]

theorem cmp116Eq224_localized_gaussianMajorant_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (r : ι → ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖R‖ ^ 2 < 1) :
    cmp116Eq224GaussianMajorant R
        (-(alpha • cmp116Eq223CoordinateProjection S))
        (fun i => (r i : ℂ)) ≤
      (Real.sqrt
        ((1 - alpha * ‖R‖ ^ 2) ^ Fintype.card ι))⁻¹ *
        Real.exp
          ((‖R‖ ^ 2 * (r ⬝ᵥ r)) /
            (2 * (1 - alpha * ‖R‖ ^ 2))) := by
  simp only [cmp116Eq224GaussianMajorant]
  have hmatrix :
      (1 + Rᵀ * (-(alpha • cmp116Eq223CoordinateProjection S)) * R) =
        1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R := by
    noncomm_ring
  rw [hmatrix]
  apply mul_le_mul
  · exact inv_sqrt_det_one_sub_localized_covariance_le
      S R alpha (‖R‖ ^ 2) halpha
      (dotProduct_mulVec_self_le_l2_opNorm_sq R) hsmall
  · exact Real.exp_le_exp.mpr
      (cmp116Eq224_localized_source_re_le S R alpha r halpha hsmall)
  · exact Real.exp_nonneg _
  · positivity

end

end YangMills.RG
