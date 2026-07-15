/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223PhysicalSmallness

/-!
# CMP116 equation (2.24): a quantitative localized determinant bound

The exact finite-dimensional Gaussian evaluation produces the determinant
factor

`det (I - Rᵀ (alpha P_Z0) R)⁻¹/²`.

This module bounds it explicitly.  The generic spectral result says that if a
positive-semidefinite matrix `H` satisfies `xᵀHx ≤ q xᵀx` with `q < 1`, then

`(1 - q)^n ≤ det (I - H)`.

For the localized CMP116 Hessian, the already formalized facts `P_Z0 ≤ I` and
`‖R x‖² ≤ covarianceBound * ‖x‖²` give `q = alpha * covarianceBound`.
Consequently the determinant part of the (2.24) majorant is no longer a free
analytic hypothesis.

Honest scope: this module bounds the determinant prefactor.  It does not yet
bound the completed-square source exponential in (2.24), identify the
model-specific uniform constants in (2.26), or prove `hraw`/`hRpoly`.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- Spectral product formula for `det (I - H)` when `H` is positive
semidefinite. -/
theorem det_one_sub_eq_prod_eigenvalues_of_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosSemidef) :
    Matrix.det (1 - H) = ∏ i, (1 - hH.isHermitian.eigenvalues i) := by
  let U := hH.isHermitian.eigenvectorUnitary
  let eigs := hH.isHermitian.eigenvalues
  have hspec :
      H = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
        (Matrix.diagonal eigs) := by
    simpa [eigs] using hH.isHermitian.spectral_theorem
  calc
    Matrix.det (1 - H) = Matrix.det
        (1 - Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
          (Matrix.diagonal eigs)) := by rw [hspec]
    _ = ∏ i, (1 - eigs i) := by
      rw [Unitary.conjStarAlgAut_apply]
      have hunit :
          (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := by
        exact Unitary.coe_mul_star_self U
      have hfactor :
          1 - (U : Matrix ι ι ℝ) * Matrix.diagonal eigs *
                star (U : Matrix ι ι ℝ) =
            (U : Matrix ι ι ℝ) * (1 - Matrix.diagonal eigs) *
              star (U : Matrix ι ι ℝ) := by
        symm
        calc
          (U : Matrix ι ι ℝ) * (1 - Matrix.diagonal eigs) *
                star (U : Matrix ι ι ℝ) =
              ((U : Matrix ι ι ℝ) * 1 -
                (U : Matrix ι ι ℝ) * Matrix.diagonal eigs) *
                  star (U : Matrix ι ι ℝ) := by rw [mul_sub]
          _ = (U : Matrix ι ι ℝ) * 1 * star (U : Matrix ι ι ℝ) -
                (U : Matrix ι ι ℝ) * Matrix.diagonal eigs *
                  star (U : Matrix ι ι ℝ) := by rw [sub_mul]
          _ = 1 - (U : Matrix ι ι ℝ) * Matrix.diagonal eigs *
                star (U : Matrix ι ι ℝ) := by
              rw [mul_one, hunit]
      rw [hfactor, Matrix.det_mul, Matrix.det_mul]
      have hdetunit :
          Matrix.det (U : Matrix ι ι ℝ) *
              Matrix.det (star (U : Matrix ι ι ℝ)) = 1 := by
        rw [← Matrix.det_mul, hunit, Matrix.det_one]
      have hdiag :
          (1 - Matrix.diagonal eigs : Matrix ι ι ℝ) =
            Matrix.diagonal (fun i => 1 - eigs i) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
      rw [hdiag, Matrix.det_diagonal]
      calc
        Matrix.det (U : Matrix ι ι ℝ) * (∏ i, (1 - eigs i)) *
              Matrix.det (star (U : Matrix ι ι ℝ)) =
            (∏ i, (1 - eigs i)) *
              (Matrix.det (U : Matrix ι ι ℝ) *
                Matrix.det (star (U : Matrix ι ι ℝ))) := by ring
        _ = ∏ i, (1 - eigs i) := by rw [hdetunit, mul_one]
    _ = ∏ i, (1 - hH.isHermitian.eigenvalues i) := by rfl

/-- A quadratic-form upper bound controls every eigenvalue of a
positive-semidefinite matrix. -/
theorem eigenvalue_le_of_posSemidef_quadratic_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosSemidef) (q : ℝ)
    (hupper : ∀ x : ι → ℝ,
      x ⬝ᵥ (H *ᵥ x) ≤ q * (x ⬝ᵥ x)) (i : ι) :
    hH.isHermitian.eigenvalues i ≤ q := by
  let v : ι → ℝ := ⇑(hH.isHermitian.eigenvectorBasis i)
  have h := hupper v
  have hvne : v ≠ 0 := by
    simpa [v] using hH.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
  have hvpos : 0 < v ⬝ᵥ v := by
    have hnonneg : 0 ≤ v ⬝ᵥ v := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    have hne : v ⬝ᵥ v ≠ 0 := by
      intro hzero
      exact hvne (dotProduct_self_eq_zero.mp hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have heig : H *ᵥ v = (hH.isHermitian.eigenvalues i) • v :=
    hH.isHermitian.mulVec_eigenvectorBasis i
  rw [heig, dotProduct_smul] at h
  simp only [smul_eq_mul] at h
  nlinarith

/-- Quantitative determinant lower bound obtained from a uniform quadratic
bound on a positive-semidefinite matrix. -/
theorem pow_card_le_det_one_sub_of_posSemidef_quadratic_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosSemidef) (q : ℝ)
    (hq : q < 1)
    (hupper : ∀ x : ι → ℝ,
      x ⬝ᵥ (H *ᵥ x) ≤ q * (x ⬝ᵥ x)) :
    (1 - q) ^ Fintype.card ι ≤ Matrix.det (1 - H) := by
  rw [det_one_sub_eq_prod_eigenvalues_of_posSemidef H hH]
  have hbase : 0 ≤ 1 - q := by linarith
  have hterm : ∀ i : ι,
      1 - q ≤ 1 - hH.isHermitian.eigenvalues i := by
    intro i
    linarith [eigenvalue_le_of_posSemidef_quadratic_upper
      H hH q hupper i]
  simpa using (Finset.prod_le_prod
    (fun _ _ => hbase)
    (fun i _ => hterm i) :
      (∏ _i : ι, (1 - q)) ≤
        ∏ i : ι, (1 - hH.isHermitian.eigenvalues i))

/-- Inverse-square-root form of the generic determinant estimate. -/
theorem inv_sqrt_det_one_sub_le_of_posSemidef_quadratic_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosSemidef) (q : ℝ)
    (hq : q < 1)
    (hupper : ∀ x : ι → ℝ,
      x ⬝ᵥ (H *ᵥ x) ≤ q * (x ⬝ᵥ x)) :
    (Real.sqrt (Matrix.det (1 - H)))⁻¹ ≤
      (Real.sqrt ((1 - q) ^ Fintype.card ι))⁻¹ := by
  have hbasepos : 0 < (1 - q) ^ Fintype.card ι :=
    pow_pos (sub_pos.mpr hq) _
  have hdetlower :=
    pow_card_le_det_one_sub_of_posSemidef_quadratic_upper
      H hH q hq hupper
  have hdetpos : 0 < Matrix.det (1 - H) := hbasepos.trans_le hdetlower
  have hsqrtle :
      Real.sqrt ((1 - q) ^ Fintype.card ι) ≤
        Real.sqrt (Matrix.det (1 - H)) :=
    Real.sqrt_le_sqrt hdetlower
  exact (inv_le_inv₀ (Real.sqrt_pos.2 hdetpos)
    (Real.sqrt_pos.2 hbasepos)).2 hsqrtle

/-- The localized covariance Hessian is positive semidefinite. -/
theorem posSemidef_localized_covariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (halpha : 0 ≤ alpha) :
    (Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R).PosSemidef := by
  exact
    ((cmp116Eq223CoordinateProjection_posSemidef S).smul halpha).conjTranspose_mul_mul_same R

/-- `P_Z0 ≤ I` turns the covariance-root estimate into the quadratic upper
bound required by the determinant theorem. -/
theorem quadratic_localized_covariance_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha covarianceBound : ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ x : ι → ℝ,
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ covarianceBound * (x ⬝ᵥ x)) :
    ∀ x : ι → ℝ,
      x ⬝ᵥ ((Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) *ᵥ x) ≤
        (alpha * covarianceBound) * (x ⬝ᵥ x) := by
  intro x
  have hproj := dotProduct_projection_mulVec_le_self S (R *ᵥ x)
  have hquad :
      x ⬝ᵥ ((Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) *ᵥ x) =
        alpha * ((R *ᵥ x) ⬝ᵥ
          (cmp116Eq223CoordinateProjection S *ᵥ (R *ᵥ x))) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
    rw [smul_mulVec, dotProduct_smul]
    simp only [smul_eq_mul]
  rw [hquad]
  calc
    alpha * ((R *ᵥ x) ⬝ᵥ
        (cmp116Eq223CoordinateProjection S *ᵥ (R *ᵥ x))) ≤
        alpha * ((R *ᵥ x) ⬝ᵥ (R *ᵥ x)) :=
      mul_le_mul_of_nonneg_left hproj halpha
    _ ≤ alpha * (covarianceBound * (x ⬝ᵥ x)) :=
      mul_le_mul_of_nonneg_left (hcov x) halpha
    _ = (alpha * covarianceBound) * (x ⬝ᵥ x) := by ring

/-- Determinant lower bound for the literal localized CMP116 Hessian. -/
theorem det_one_sub_localized_covariance_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha covarianceBound : ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ x : ι → ℝ,
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ covarianceBound * (x ⬝ᵥ x))
    (hsmall : alpha * covarianceBound < 1) :
    (1 - alpha * covarianceBound) ^ Fintype.card ι ≤
      Matrix.det
        (1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) := by
  exact pow_card_le_det_one_sub_of_posSemidef_quadratic_upper
    (Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R)
    (posSemidef_localized_covariance S R alpha halpha)
    (alpha * covarianceBound) hsmall
    (quadratic_localized_covariance_le
      S R alpha covarianceBound halpha hcov)

/-- Inverse-square-root determinant bound for the localized covariance
Hessian. -/
theorem inv_sqrt_det_one_sub_localized_covariance_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha covarianceBound : ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ x : ι → ℝ,
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ covarianceBound * (x ⬝ᵥ x))
    (hsmall : alpha * covarianceBound < 1) :
    (Real.sqrt (Matrix.det
      (1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R)))⁻¹ ≤
      (Real.sqrt ((1 - alpha * covarianceBound) ^ Fintype.card ι))⁻¹ := by
  exact inv_sqrt_det_one_sub_le_of_posSemidef_quadratic_upper
    (Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R)
    (posSemidef_localized_covariance S R alpha halpha)
    (alpha * covarianceBound) hsmall
    (quadratic_localized_covariance_le
      S R alpha covarianceBound halpha hcov)

/-- The determinant prefactor in the literal sign convention of the CMP116
(2.24) Gaussian majorant. -/
theorem cmp116Eq224_localized_determinant_prefactor_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha covarianceBound : ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ x : ι → ℝ,
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ covarianceBound * (x ⬝ᵥ x))
    (hsmall : alpha * covarianceBound < 1) :
    (Real.sqrt (Matrix.det
      (1 + Rᵀ * (-(alpha • cmp116Eq223CoordinateProjection S)) * R)))⁻¹ ≤
      (Real.sqrt ((1 - alpha * covarianceBound) ^ Fintype.card ι))⁻¹ := by
  have hmatrix :
      (1 + Rᵀ * (-(alpha • cmp116Eq223CoordinateProjection S)) * R) =
        1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R := by
    noncomm_ring
  rw [hmatrix]
  exact inv_sqrt_det_one_sub_localized_covariance_le
    S R alpha covarianceBound halpha hcov hsmall

end

end YangMills.RG
