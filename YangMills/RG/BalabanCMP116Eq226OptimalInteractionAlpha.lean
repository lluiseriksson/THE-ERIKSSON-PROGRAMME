/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq225SourceEnergy

/-!
# The optimal scalar interaction budget in CMP116 equation (2.26)

The interaction estimate forces

`potentialRate + r2Rate + gamma ≤ alpha`.

Both Gaussian smallness conditions become harder when `alpha` is enlarged.
Consequently the canonical choice is the lower endpoint

`alpha = potentialRate + r2Rate + gamma`.

This file records that normalization and writes the two remaining scalar
stability obligations without hiding the completed-square denominator.  It
does not prove either smallness inequality and therefore does not replace any
model-specific estimate.
-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The smallest interaction coefficient allowed by the three physical
quadratic contributions. -/
def cmp116Eq226OptimalInteractionAlpha
    (potentialRate r2Rate gamma : ℝ) : ℝ :=
  potentialRate + r2Rate + gamma

/-- Choosing the lower endpoint closes the bookkeeping inequality by
reflexivity.  This is a normalization, not an analytic estimate. -/
theorem cmp116Eq226_optimalInteractionAlpha_budget
    (potentialRate r2Rate gamma : ℝ) :
    potentialRate + r2Rate + gamma ≤
      cmp116Eq226OptimalInteractionAlpha potentialRate r2Rate gamma := by
  rfl

/-- Nonnegativity of the normalized coefficient remains exactly the
nonnegativity of the sum of the three rates. -/
theorem cmp116Eq226_optimalInteractionAlpha_nonneg_iff
    (potentialRate r2Rate gamma : ℝ) :
    0 ≤ cmp116Eq226OptimalInteractionAlpha potentialRate r2Rate gamma ↔
      0 ≤ potentialRate + r2Rate + gamma := by
  rfl

/-- The first genuine scalar obligation after the optimal normalization:
the total interaction rate must lie below the inverse covariance scale. -/
def CMP116Eq226OptimalCovarianceSmall
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (potentialRate r2Rate gamma : ℝ) : Prop :=
  cmp116Eq226OptimalInteractionAlpha potentialRate r2Rate gamma *
      ‖R‖ ^ 2 < 1

/-- The second genuine scalar obligation, written with the explicit
completed-square denominator rather than an opaque coefficient. -/
def CMP116Eq226OptimalGaussianSmall
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ)
    (potentialRate r2Rate gamma outerRate sourceRate : ℝ) : Prop :=
  2 * (outerRate +
    (‖R‖ ^ 2 * sourceRate) /
      (2 * (1 -
        cmp116Eq226OptimalInteractionAlpha potentialRate r2Rate gamma *
          ‖R‖ ^ 2))) < 1

/-- The covariance condition consumed by the terminal source record is
definitionally the first normalized stability obligation. -/
theorem cmp116Eq226_optimalCovarianceSmall_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (potentialRate r2Rate gamma : ℝ) :
    cmp116Eq226OptimalInteractionAlpha potentialRate r2Rate gamma *
        ‖R‖ ^ 2 < 1 ↔
      CMP116Eq226OptimalCovarianceSmall
        R potentialRate r2Rate gamma := by
  rfl

/-- After unfolding `(2.25)`, the Gaussian condition consumed by the terminal
record is exactly the second normalized stability obligation. -/
theorem cmp116Eq226_optimalGaussianSmall_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ)
    (potentialRate r2Rate gamma outerRate sourceRate : ℝ) :
    2 * (outerRate +
      cmp116Eq225SourceCoefficient R
          (cmp116Eq226OptimalInteractionAlpha
            potentialRate r2Rate gamma) *
        sourceRate) < 1 ↔
      CMP116Eq226OptimalGaussianSmall R
        potentialRate r2Rate gamma outerRate sourceRate := by
  simp only [CMP116Eq226OptimalGaussianSmall,
    cmp116Eq225SourceCoefficient, div_mul_eq_mul_div]

end

end YangMills.RG
