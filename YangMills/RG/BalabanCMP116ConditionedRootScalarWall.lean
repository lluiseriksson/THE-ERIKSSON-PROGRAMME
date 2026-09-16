/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226OptimalInteractionAlpha
import YangMills.RG.BalabanCMP116MatrixGaussianCarrier

/-!
# The conditioned-root scalar wall in CMP116

Validated in a fresh Colab CPU/high-RAM clone at source checkpoint
`4cf34623cf6096f89653cd9fb1c3dc848a7e9294`; the focal audit and root build
both exited zero.

The terminal conditioned Gaussian supplies a symmetric finite matrix `R`
whose square is the conditioned covariance `C`.  The matrix C-star identity
therefore gives the exact equality `‖R‖² = ‖C‖`.

If a separate physical compression theorem supplies `‖C‖ ≤ c⁻¹`, the two
terminal scalar walls reduce to `A < c` and
`2 * outerRate + sourceRate / (c - A) < 1`, where
`A = potentialRate + r2Rate + gamma`.

This file proves only that universal reduction.  It deliberately does not
identify `C` with a localized compression of the interacting covariance and
does not manufacture the bound `‖C‖ ≤ c⁻¹`; that remains the source-facing
Poincare/Combes--Thomas bridge.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A symmetric finite Gaussian root has squared operator norm exactly equal
to the norm of the covariance that it squares to. -/
theorem norm_conditionedRoot_sq_eq_covariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C R : Matrix ι ι ℝ} {S : Finset ι}
    (hroot : MatrixConditionedGaussianRootCertificate C R S) :
    ‖R‖ ^ 2 = ‖C‖ := by
  calc
    ‖R‖ ^ 2 = ‖R‖ * ‖R‖ := by rw [pow_two]
    _ = ‖Rᴴ * R‖ := (Matrix.l2_opNorm_conjTranspose_mul_self R).symm
    _ = ‖R * R‖ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        hroot.root_symmetric]
    _ = ‖C‖ := by rw [hroot.root_square]

/-- An inverse-coercivity upper bound on the covariance norm turns `A < c`
into the first terminal Gaussian smallness inequality. -/
theorem mul_conditionedRoot_norm_sq_lt_one_of_lt_coercivity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} {A c : ℝ}
    (hc : 0 < c)
    (hA : A < c)
    (hroot : ‖R‖ ^ 2 ≤ c⁻¹) :
    A * ‖R‖ ^ 2 < 1 := by
  have hx0 : 0 ≤ ‖R‖ ^ 2 := sq_nonneg ‖R‖
  have hcx : c * ‖R‖ ^ 2 ≤ 1 := by
    calc
      c * ‖R‖ ^ 2 ≤ c * c⁻¹ :=
        mul_le_mul_of_nonneg_left hroot hc.le
      _ = 1 := by simp [hc.ne']
  by_cases hx : ‖R‖ ^ 2 = 0
  · simp [hx]
  · have hxpos : 0 < ‖R‖ ^ 2 := lt_of_le_of_ne hx0 (Ne.symm hx)
    exact (mul_lt_mul_of_pos_right hA hxpos).trans_le hcx

/-- The completed-square source coefficient is bounded by the remaining
coercivity gap.  This is the exact scalar cancellation behind the second
terminal wall. -/
theorem cmp116Eq225SourceCoefficient_le_inv_two_mul_coercivity_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} {A c : ℝ}
    (hc : 0 < c)
    (hA : A < c)
    (hroot : ‖R‖ ^ 2 ≤ c⁻¹) :
    cmp116Eq225SourceCoefficient R A ≤ 1 / (2 * (c - A)) := by
  have hsmall : A * ‖R‖ ^ 2 < 1 :=
    mul_conditionedRoot_norm_sq_lt_one_of_lt_coercivity hc hA hroot
  have hleft : 0 < 2 * (1 - A * ‖R‖ ^ 2) := by
    exact mul_pos (by norm_num) (sub_pos.mpr hsmall)
  have hright : 0 < 2 * (c - A) := by
    exact mul_pos (by norm_num) (sub_pos.mpr hA)
  have hcx : c * ‖R‖ ^ 2 ≤ 1 := by
    calc
      c * ‖R‖ ^ 2 ≤ c * c⁻¹ :=
        mul_le_mul_of_nonneg_left hroot hc.le
      _ = 1 := by simp [hc.ne']
  unfold cmp116Eq225SourceCoefficient
  apply (div_le_div_iff₀ hleft hright).2
  nlinarith

/-- The inverse-coercivity covariance bound and `A < c` discharge the first
normalized terminal wall. -/
theorem cmp116Eq226_optimalCovarianceSmall_of_conditionedCovarianceNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C R : Matrix ι ι ℝ} {S : Finset ι}
    {potentialRate r2Rate gamma c : ℝ}
    (hcert : MatrixConditionedGaussianRootCertificate C R S)
    (hc : 0 < c)
    (hA : cmp116Eq226OptimalInteractionAlpha
      potentialRate r2Rate gamma < c)
    (hcovariance : ‖C‖ ≤ c⁻¹) :
    CMP116Eq226OptimalCovarianceSmall
      R potentialRate r2Rate gamma := by
  unfold CMP116Eq226OptimalCovarianceSmall
  apply mul_conditionedRoot_norm_sq_lt_one_of_lt_coercivity hc hA
  rwa [norm_conditionedRoot_sq_eq_covariance hcert]

/-- Under the same root bound, the explicit remaining-gap budget is a
sufficient condition for the second normalized terminal wall. -/
theorem cmp116Eq226_optimalGaussianSmall_of_conditionedCovarianceNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C R : Matrix ι ι ℝ} {S : Finset ι}
    {potentialRate r2Rate gamma outerRate sourceRate c : ℝ}
    (hcert : MatrixConditionedGaussianRootCertificate C R S)
    (hc : 0 < c)
    (hA : cmp116Eq226OptimalInteractionAlpha
      potentialRate r2Rate gamma < c)
    (hsource : 0 ≤ sourceRate)
    (hcovariance : ‖C‖ ≤ c⁻¹)
    (hbudget : 2 * outerRate + sourceRate /
      (c - cmp116Eq226OptimalInteractionAlpha
        potentialRate r2Rate gamma) < 1) :
    CMP116Eq226OptimalGaussianSmall R
      potentialRate r2Rate gamma outerRate sourceRate := by
  let A := cmp116Eq226OptimalInteractionAlpha
    potentialRate r2Rate gamma
  have hroot : ‖R‖ ^ 2 ≤ c⁻¹ := by
    rwa [norm_conditionedRoot_sq_eq_covariance hcert]
  have hcoeff :=
    cmp116Eq225SourceCoefficient_le_inv_two_mul_coercivity_sub
      (R := R) (A := A) hc hA hroot
  have hcoeffSource := mul_le_mul_of_nonneg_right hcoeff hsource
  have hcoeffSource' :
      cmp116Eq225SourceCoefficient R
          (cmp116Eq226OptimalInteractionAlpha
            potentialRate r2Rate gamma) * sourceRate ≤
        (1 / (2 * (c - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma))) * sourceRate := by
    simpa [A] using hcoeffSource
  have hgap : 0 < c - cmp116Eq226OptimalInteractionAlpha
      potentialRate r2Rate gamma := sub_pos.mpr hA
  have hscaled :
      2 * (cmp116Eq225SourceCoefficient R
          (cmp116Eq226OptimalInteractionAlpha
            potentialRate r2Rate gamma) * sourceRate) ≤
        sourceRate / (c - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma) := by
    calc
      2 * (cmp116Eq225SourceCoefficient R
          (cmp116Eq226OptimalInteractionAlpha
            potentialRate r2Rate gamma) * sourceRate) ≤
        2 * ((1 / (2 * (c - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma))) * sourceRate) := by
            exact mul_le_mul_of_nonneg_left hcoeffSource' (by norm_num)
      _ = sourceRate / (c - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma) := by
            field_simp [hgap.ne']
  have hscaledTerm :
      2 * (‖R‖ ^ 2 * sourceRate /
        (2 * (1 - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma * ‖R‖ ^ 2))) ≤
        sourceRate / (c - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma) := by
    calc
      2 * (‖R‖ ^ 2 * sourceRate /
        (2 * (1 - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma * ‖R‖ ^ 2))) =
        2 * (cmp116Eq225SourceCoefficient R
          (cmp116Eq226OptimalInteractionAlpha
            potentialRate r2Rate gamma) * sourceRate) := by
              unfold cmp116Eq225SourceCoefficient
              ring
      _ ≤ sourceRate / (c - cmp116Eq226OptimalInteractionAlpha
          potentialRate r2Rate gamma) := hscaled
  unfold CMP116Eq226OptimalGaussianSmall
  nlinarith

end

end YangMills.RG
