/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq224DeterminantBound
import YangMills.RG.BalabanCMP116Eq223CovarianceOpNorm
import YangMills.RG.BalabanCMP116Eq224SourceBound
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# CMP116 equation (2.24): rank-localized determinant

The perturbation `Rᵀ (alpha P_S) R` acts through the finite carrier `S`.
Weinstein--Aronszajn therefore moves its determinant from the full Gaussian
space to a matrix indexed by `S`.  The existing spectral estimate can then be
applied in dimension `|S|`, yielding

`det (I - alpha Rᵀ P_S R) >= (1 - alpha ‖R‖²)^|S|`.

This removes the ambient-volume exponent from the determinant contribution to
the CMP116 Gaussian majorant.  It does not identify the concrete `Gamma_k`
source kernel or close the remaining polymer ledger in (2.26).
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-- Restrict the output rows of a square matrix to a finite carrier. -/
def cmp116FinsetRowRestriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) : Matrix S ι ℝ :=
  R.submatrix Subtype.val id

/-- The rectangular factorization recovers the literal localized covariance. -/
theorem transpose_mul_restriction_eq_localizedCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ) :
    (cmp116FinsetRowRestriction S R)ᵀ *
        (alpha • cmp116FinsetRowRestriction S R) =
      Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R := by
  ext i j
  simp [cmp116FinsetRowRestriction, Matrix.mul_apply,
    cmp116Eq223CoordinateProjection, Matrix.diagonal]
  calc
    (∑ x ∈ S.attach, R (x : ι) i * (alpha * R (x : ι) j)) =
        ∑ x ∈ S, R x i * (alpha * R x j) :=
      Finset.sum_attach S (fun x => R x i * (alpha * R x j))
    _ = ∑ x ∈ S, R x i * alpha * R x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (mul_assoc (R x i) alpha (R x j)).symm

/-- Extend a vector on a finite carrier by zero. -/
def cmp116FinsetExtend
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : S → ℝ) : ι → ℝ :=
  fun i => if hi : i ∈ S then x ⟨i, hi⟩ else 0

/-- Zero extension agrees with the original vector on its carrier. -/
@[simp] theorem cmp116FinsetExtend_apply_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : S → ℝ) (i : S) :
    cmp116FinsetExtend S x i = x i := by
  simp [cmp116FinsetExtend, i.property]

/-- Restriction and zero extension are adjoint for the Euclidean pairing. -/
theorem dotProduct_restrict_eq_dotProduct_extend
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (x : S → ℝ) :
    (fun s : S => f s) ⬝ᵥ x = f ⬝ᵥ cmp116FinsetExtend S x := by
  rw [dotProduct, dotProduct]
  calc
    (∑ s : S, f s * x s) =
        ∑ s : S, f s * cmp116FinsetExtend S x s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [cmp116FinsetExtend_apply_mem]
    _ = ∑ i ∈ S, f i * cmp116FinsetExtend S x i := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach S
        (fun i => f i * cmp116FinsetExtend S x i)
    _ = ∑ i, f i * cmp116FinsetExtend S x i := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hi hinot
      simp [cmp116FinsetExtend, hinot]

/-- Zero extension preserves the Euclidean quadratic form. -/
theorem dotProduct_cmp116FinsetExtend
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : S → ℝ) :
    cmp116FinsetExtend S x ⬝ᵥ cmp116FinsetExtend S x = x ⬝ᵥ x := by
  symm
  simpa using dotProduct_restrict_eq_dotProduct_extend
    S (cmp116FinsetExtend S x) x

/-- The transpose of row restriction equals the full transpose after zero
extension. -/
theorem transpose_restriction_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (x : S → ℝ) :
    (cmp116FinsetRowRestriction S R)ᵀ *ᵥ x =
      Rᵀ *ᵥ cmp116FinsetExtend S x := by
  ext j
  simp only [cmp116FinsetRowRestriction, Matrix.mulVec,
    Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  exact dotProduct_restrict_eq_dotProduct_extend S (fun i => R i j) x

/-- Weinstein--Aronszajn moves the determinant to the carrier-indexed space. -/
theorem det_one_sub_localizedCovariance_eq_restriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ) :
    Matrix.det
        (1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) =
      Matrix.det
        (1 - (alpha • cmp116FinsetRowRestriction S R) *
          (cmp116FinsetRowRestriction S R)ᵀ) := by
  rw [← transpose_mul_restriction_eq_localizedCovariance]
  exact Matrix.det_one_sub_mul_comm
    (cmp116FinsetRowRestriction S R)ᵀ
    (alpha • cmp116FinsetRowRestriction S R)

/-- The carrier-indexed covariance perturbation is positive semidefinite. -/
theorem posSemidef_restricted_localizedCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (halpha : 0 ≤ alpha) :
    ((alpha • cmp116FinsetRowRestriction S R) *
      (cmp116FinsetRowRestriction S R)ᵀ).PosSemidef := by
  have h := (Matrix.PosSemidef.one.smul halpha).mul_mul_conjTranspose_same
    (cmp116FinsetRowRestriction S R)
  simpa only [Matrix.mul_smul, Matrix.mul_one,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The restricted perturbation inherits the full `L²` operator-norm bound. -/
theorem quadratic_restricted_localizedCovariance_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (halpha : 0 ≤ alpha) :
    ∀ x : S → ℝ,
      x ⬝ᵥ (((alpha • cmp116FinsetRowRestriction S R) *
        (cmp116FinsetRowRestriction S R)ᵀ) *ᵥ x) ≤
      (alpha * ‖R‖ ^ 2) * (x ⬝ᵥ x) := by
  intro x
  let C := cmp116FinsetRowRestriction S R
  have hRt : ‖Rᵀ‖ = ‖R‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose R
  have hrestricted :
      (Cᵀ *ᵥ x) ⬝ᵥ (Cᵀ *ᵥ x) ≤ ‖R‖ ^ 2 * (x ⬝ᵥ x) := by
    have h := dotProduct_mulVec_self_le_l2_opNorm_sq
      Rᵀ (cmp116FinsetExtend S x)
    rw [hRt, dotProduct_cmp116FinsetExtend S x] at h
    rw [transpose_restriction_mulVec]
    exact h
  have hquad :
      x ⬝ᵥ (((alpha • C) * Cᵀ) *ᵥ x) =
        alpha * ((Cᵀ *ᵥ x) ⬝ᵥ (Cᵀ *ᵥ x)) := by
    have hv : x ᵥ* C = Cᵀ *ᵥ x := by
      simpa using (vecMul_transpose Cᵀ x)
    rw [← mulVec_mulVec, smul_mulVec, dotProduct_smul,
      dotProduct_mulVec, hv]
    simp only [smul_eq_mul]
  rw [show cmp116FinsetRowRestriction S R = C by rfl, hquad]
  calc
    alpha * ((Cᵀ *ᵥ x) ⬝ᵥ (Cᵀ *ᵥ x)) ≤
        alpha * (‖R‖ ^ 2 * (x ⬝ᵥ x)) :=
      mul_le_mul_of_nonneg_left hrestricted halpha
    _ = (alpha * ‖R‖ ^ 2) * (x ⬝ᵥ x) := by ring

/-- Determinant lower bound with exponent exactly `|S|`. -/
theorem pow_card_localized_le_det_one_sub_localizedCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (halpha : 0 ≤ alpha) (hsmall : alpha * ‖R‖ ^ 2 < 1) :
    (1 - alpha * ‖R‖ ^ 2) ^ S.card ≤
      Matrix.det
        (1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) := by
  rw [det_one_sub_localizedCovariance_eq_restriction]
  simpa using pow_card_le_det_one_sub_of_posSemidef_quadratic_upper
    ((alpha • cmp116FinsetRowRestriction S R) *
      (cmp116FinsetRowRestriction S R)ᵀ)
    (posSemidef_restricted_localizedCovariance S R alpha halpha)
    (alpha * ‖R‖ ^ 2) hsmall
    (quadratic_restricted_localizedCovariance_le S R alpha halpha)

/-- Inverse-square-root determinant bound with no ambient-volume exponent. -/
theorem inv_sqrt_det_one_sub_localizedCovariance_le_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (halpha : 0 ≤ alpha) (hsmall : alpha * ‖R‖ ^ 2 < 1) :
    (Real.sqrt (Matrix.det
      (1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R)))⁻¹ ≤
      (Real.sqrt ((1 - alpha * ‖R‖ ^ 2) ^ S.card))⁻¹ := by
  rw [det_one_sub_localizedCovariance_eq_restriction]
  simpa using inv_sqrt_det_one_sub_le_of_posSemidef_quadratic_upper
    ((alpha • cmp116FinsetRowRestriction S R) *
      (cmp116FinsetRowRestriction S R)ᵀ)
    (posSemidef_restricted_localizedCovariance S R alpha halpha)
    (alpha * ‖R‖ ^ 2) hsmall
    (quadratic_restricted_localizedCovariance_le S R alpha halpha)

/-- The complete (2.24) majorant with determinant exponent `|S|`. -/
theorem cmp116Eq224_localized_gaussianMajorant_le_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (r : ι → ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖R‖ ^ 2 < 1) :
    cmp116Eq224GaussianMajorant R
        (-(alpha • cmp116Eq223CoordinateProjection S))
        (fun i => (r i : ℂ)) ≤
      (Real.sqrt ((1 - alpha * ‖R‖ ^ 2) ^ S.card))⁻¹ *
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
  · exact inv_sqrt_det_one_sub_localizedCovariance_le_card
      S R alpha halpha hsmall
  · exact Real.exp_le_exp.mpr
      (cmp116Eq224_localized_source_re_le S R alpha r halpha hsmall)
  · exact Real.exp_nonneg _
  · positivity

end
end YangMills.RG
