/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223PhysicalSmallness
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# CMP116 equation (2.23): covariance-root operator-norm bound

The localized Gaussian smallness module reduces positivity of

`I - alpha * Rᵀ P_Z0 R`

to a quadratic covariance-root bound and the scalar condition
`alpha * covarianceBound < 1`.  This module supplies the canonical finite-
dimensional choice

`covarianceBound = ‖R‖²`,

where the norm is the matrix `L²` operator norm.  Thus the quadratic bound is
no longer an external hypothesis: it follows directly from the definition of
the operator norm.

The terminal endpoint feeds the resulting positivity theorem into the
dominated Gaussian estimate for the literal CMP116 finite-Gaussian data.

Honest scope: this module does not yet identify `R`, `alpha`, or the localized
coordinate set with every concrete field-theoretic object in CMP116 (2.14),
nor does it prove the scalar smallness condition for that concrete covariance.
It removes the separate abstract `hcov` obligation once those data are given.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The squared `L²` operator norm supplies the canonical quadratic bound for
any finite real covariance root. -/
theorem dotProduct_mulVec_self_le_l2_opNorm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (x : ι → ℝ) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ x) ≤ ‖R‖ ^ 2 * (x ⬝ᵥ x) := by
  let xE : EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm x
  let yE : EuclideanSpace ℝ ι :=
    (EuclideanSpace.equiv ι ℝ).symm (R *ᵥ x)
  have hnorm : ‖yE‖ ≤ ‖R‖ * ‖xE‖ := by
    simpa [xE, yE] using R.l2_opNorm_mulVec xE
  have hsq : ‖yE‖ ^ 2 ≤ (‖R‖ * ‖xE‖) ^ 2 := by
    exact (sq_le_sq₀
      (norm_nonneg yE)
      (mul_nonneg (norm_nonneg R) (norm_nonneg xE))).2 hnorm
  rw [EuclideanSpace.real_norm_sq_eq yE, mul_pow,
    EuclideanSpace.real_norm_sq_eq xE] at hsq
  simpa [xE, yE, dotProduct, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

/-- The physical localized shifted Hessian is positive whenever the scalar
coefficient times the squared covariance-root operator norm is below one. -/
theorem posDef_one_sub_localized_covariance_of_l2_opNorm_small
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖R‖ ^ 2 < 1) :
    (1 - Rᵀ * (alpha • cmp116Eq223CoordinateProjection S) * R).PosDef := by
  exact posDef_one_sub_localized_covariance_of_small
    S R alpha (‖R‖ ^ 2) halpha
    (dotProduct_mulVec_self_le_l2_opNorm_sq R) hsmall

/-- Apply the canonical covariance-root norm bound directly to the dominated
inner Gaussian estimate.  Unlike the preceding localized-smallness endpoint,
this theorem exposes no separate covariance quadratic-bound hypothesis. -/
theorem CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_eq224Majorant_of_l2OpNormSmallness
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate Bond lieDim)
    (localizedCoordinates : Finset (Bond × Fin lieDim))
    (alpha : ℝ)
    (r : Bond × Fin lieDim → ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖G.covarianceRoot sigma tau‖ ^ 2 < 1)
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
  exact G.norm_innerIntegral_le_eq224Majorant_of_localizedSmallness
    Y0 P sigma tau psi phi x localizedCoordinates
    alpha (‖G.covarianceRoot sigma tau‖ ^ 2) r halpha
    (dotProduct_mulVec_self_le_l2_opNorm_sq (G.covarianceRoot sigma tau))
    hsmall hdom

end YangMills.RG
