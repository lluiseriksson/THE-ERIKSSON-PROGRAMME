/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223GaussianDomination

/-!
# CMP116 equations (2.23)--(2.24): physical smallness of the localized Gaussian

The inner Gaussian in CMP116 equation (2.23) contains the positive exponential
`exp (alpha5 / 2 * ‖Z0 B‖²)`.  In the sign convention of the exact Gaussian
identity this is the negative-semidefinite perturbation

`A = -(alpha5 * P_Z0)`,

not a positive-semidefinite Hessian.  Balaban assumes
`alpha5 * ‖C^(k)(Z0, 0)‖ < 1/2` before evaluating (2.24).

This module formalizes the corresponding finite-coordinate mechanism.  It
constructs the literal diagonal projector onto the localized coordinates,
proves its exact quadratic form, and derives positivity of

`I - alpha * Rᵀ P_Z0 R`

from a covariance-root quadratic bound and the scalar smallness condition
`alpha * covarianceBound < 1`.  The terminal theorem feeds that result directly
to the dominated Gaussian estimate.

Honest scope: the module does not yet identify `alpha`, `R`, the localized
coordinate set, or the domination hypothesis with all fields and operators in
CMP116 (2.14).  It closes the exact positivity step once those physical data
are supplied.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

/-- Diagonal coordinate projector onto a finite localized carrier. -/
noncomputable def cmp116Eq223CoordinateProjection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) : Matrix ι ι ℝ :=
  diagonal fun i => if i ∈ S then 1 else 0

/-- The localized coordinate projector is positive semidefinite. -/
theorem cmp116Eq223CoordinateProjection_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    (cmp116Eq223CoordinateProjection S).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  split_ifs <;> norm_num

/-- Exact quadratic form of the localized coordinate projector. -/
theorem dotProduct_projection_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : ι → ℝ) :
    x ⬝ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x) =
      ∑ i ∈ S, x i ^ 2 := by
  rw [dotProduct]
  simp_rw [cmp116Eq223CoordinateProjection, mulVec_diagonal]
  calc
    ∑ i, x i * ((if i ∈ S then 1 else 0) * x i) =
        ∑ i, if i ∈ S then x i ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp [pow_two]
    _ = ∑ i ∈ S, x i ^ 2 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp
      · intro i hi
        simp at hi
        rfl

/-- Restricting to localized coordinates cannot increase the Euclidean
quadratic form. -/
theorem dotProduct_projection_mulVec_le_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : ι → ℝ) :
    x ⬝ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x) ≤ x ⬝ᵥ x := by
  rw [dotProduct_projection_mulVec]
  simp only [dotProduct, pow_two]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ S) (fun _ _ _ => mul_self_nonneg _)

/-- Balaban's smallness mechanism: a quadratic bound for the covariance root
and `alpha * covarianceBound < 1` make the shifted inverse covariance strictly
positive definite. -/
theorem posDef_one_sub_localized_covariance_of_small
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha covarianceBound : ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ x : ι → ℝ,
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ covarianceBound * (x ⬝ᵥ x))
    (hsmall : alpha * covarianceBound < 1) :
    (1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_one.sub
      (Matrix.isHermitian_conjTranspose_mul_mul R
        ((cmp116Eq223CoordinateProjection_posSemidef S).smul halpha).isHermitian)
  · intro x hx
    have hxpos : 0 < x ⬝ᵥ x := by
      simpa using Matrix.PosDef.one.dotProduct_mulVec_pos hx
    have hproj :
        (R *ᵥ x) ⬝ᵥ
            (cmp116Eq223CoordinateProjection S *ᵥ (R *ᵥ x)) ≤
          covarianceBound * (x ⬝ᵥ x) :=
      (dotProduct_projection_mulVec_le_self S (R *ᵥ x)).trans (hcov x)
    have hscaled :
        alpha * ((R *ᵥ x) ⬝ᵥ
          (cmp116Eq223CoordinateProjection S *ᵥ (R *ᵥ x))) <
          x ⬝ᵥ x := by
      calc
        alpha * ((R *ᵥ x) ⬝ᵥ
            (cmp116Eq223CoordinateProjection S *ᵥ (R *ᵥ x))) ≤
            alpha * (covarianceBound * (x ⬝ᵥ x)) :=
          mul_le_mul_of_nonneg_left hproj halpha
        _ = (alpha * covarianceBound) * (x ⬝ᵥ x) := by ring
        _ < 1 * (x ⬝ᵥ x) := mul_lt_mul_of_pos_right hsmall hxpos
        _ = x ⬝ᵥ x := one_mul _
    have hquad :
        x ⬝ᵥ ((Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) *ᵥ x) =
          alpha * ((R *ᵥ x) ⬝ᵥ
            (cmp116Eq223CoordinateProjection S *ᵥ (R *ᵥ x))) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
        vecMul_transpose]
      rw [smul_mulVec, dotProduct_smul]
      simp only [smul_eq_mul]
    simpa using (show
      0 < x ⬝ᵥ ((1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R) *ᵥ x) by
        rw [sub_mulVec, one_mulVec, dotProduct_sub, hquad]
        exact sub_pos.mpr hscaled)

/-- Apply the physical localized-smallness criterion directly to the dominated
inner Gaussian estimate. -/
theorem CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_eq224Majorant_of_localizedSmallness
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (localizedCoordinates : Finset (Bond × Fin lieDim))
    (alpha covarianceBound : ℝ)
    (r : Bond × Fin lieDim → ℝ)
    (halpha : 0 ≤ alpha)
    (hcov : ∀ y : Bond × Fin lieDim → ℝ,
      (G.covarianceRoot sigma tau *ᵥ y) ⬝ᵥ
          (G.covarianceRoot sigma tau *ᵥ y) ≤
        covarianceBound * (y ⬝ᵥ y))
    (hsmall : alpha * covarianceBound < 1)
    (hdom : ∀ᵐ b ∂matrixGaussianPi (G.covarianceRoot sigma tau),
      ‖G.toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b‖ ≤
          cmp116Eq223RealGaussian
            (-(alpha • cmp116Eq223CoordinateProjection localizedCoordinates)) r b) :
    ‖∫ b, G.toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b
        ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
      cmp116Eq224GaussianMajorant (G.covarianceRoot sigma tau)
        (-(alpha • cmp116Eq223CoordinateProjection localizedCoordinates))
        (fun i => (r i : ℂ)) := by
  apply G.norm_innerIntegral_le_eq224Majorant_of_domination
    Y0 P sigma tau psi phi x
    (-(alpha • cmp116Eq223CoordinateProjection localizedCoordinates)) r
  · simpa [sub_eq_add_neg] using
      posDef_one_sub_localized_covariance_of_small
        localizedCoordinates (G.covarianceRoot sigma tau)
        alpha covarianceBound halpha hcov hsmall
  · exact hdom

end YangMills.RG
