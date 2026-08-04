/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ConditionedRootScalarWall

/-!
# The conditioned-root wall at a prescribed `qBound`

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and the result has not yet been verified by the compiler.

The existing scalar-wall theorem proves the normalized Gaussian budget is
strictly below one.  The terminal centered-conditioned source asks for the
stronger, separately named comparison with its chosen `qBound`.  This module
keeps that target literal: no replacement of `qBound` by one is made.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The inverse-coercivity covariance bound controls the completed-square
source term at any prescribed `qBound`.  The last hypothesis is the remaining
literal scalar budget; the covariance root and its coefficient are discharged
inside the proof. -/
theorem cmp116Eq226_optimalOuterSmall_le_qBound_of_conditionedCovarianceNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C R : Matrix ι ι ℝ} {S : Finset ι}
    {potentialRate r2Rate gamma outerRate sourceRate c qBound : ℝ}
    (hcert : MatrixConditionedGaussianRootCertificate C R S)
    (hc : 0 < c)
    (hA : cmp116Eq226OptimalInteractionAlpha
      potentialRate r2Rate gamma < c)
    (hsource : 0 ≤ sourceRate)
    (hcovariance : ‖C‖ ≤ c⁻¹)
    (hbudget : 2 * outerRate + sourceRate /
      (c - cmp116Eq226OptimalInteractionAlpha
        potentialRate r2Rate gamma) ≤ qBound) :
    2 * (outerRate +
      |cmp116Eq225SourceCoefficient R
          (cmp116Eq226OptimalInteractionAlpha
            potentialRate r2Rate gamma) * sourceRate|) ≤ qBound := by
  let A := cmp116Eq226OptimalInteractionAlpha
    potentialRate r2Rate gamma
  have hroot : ‖R‖ ^ 2 ≤ c⁻¹ := by
    rwa [norm_conditionedRoot_sq_eq_covariance hcert]
  have hsmall : A * ‖R‖ ^ 2 < 1 :=
    mul_conditionedRoot_norm_sq_lt_one_of_lt_coercivity hc hA hroot
  have hcoeff_nonneg : 0 ≤ cmp116Eq225SourceCoefficient R A := by
    unfold cmp116Eq225SourceCoefficient
    exact div_nonneg (sq_nonneg ‖R‖)
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hsmall.le))
  have hcoeff :=
    cmp116Eq225SourceCoefficient_le_inv_two_mul_coercivity_sub
      (R := R) (A := A) hc hA hroot
  have hcoeffSource := mul_le_mul_of_nonneg_right hcoeff hsource
  have hgap : 0 < c - A := sub_pos.mpr hA
  have hscaled :
      2 * (cmp116Eq225SourceCoefficient R A * sourceRate) ≤
        sourceRate / (c - A) := by
    calc
      2 * (cmp116Eq225SourceCoefficient R A * sourceRate) ≤
          2 * ((1 / (2 * (c - A))) * sourceRate) := by
            exact mul_le_mul_of_nonneg_left hcoeffSource (by norm_num)
      _ = sourceRate / (c - A) := by field_simp [hgap.ne']
  rw [abs_of_nonneg (mul_nonneg hcoeff_nonneg hsource)]
  dsimp [A] at hbudget ⊢
  nlinarith

end

end YangMills.RG
