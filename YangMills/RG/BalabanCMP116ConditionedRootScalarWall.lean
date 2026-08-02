/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226OptimalInteractionAlpha
import YangMills.RG.BalabanCMP116MatrixGaussianCarrier

/-!
# The conditioned-root scalar wall in CMP116

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its results have not yet been verified by the Lean compiler.

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
  have hself : IsSelfAdjoint R := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hroot.root_symmetric
  calc
    ‖R‖ ^ 2 = ‖R * R‖ := hself.norm_mul_self.symm
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
    positivity
  have hright : 0 < 2 * (c - A) := by
    positivity
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
  change 2 * (outerRate +
    cmp116Eq225SourceCoefficient R A * sourceRate) < 1
  nlinarith

end

end YangMills.RG
