/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.KernelSchur

/-!
# CMP116 equation (2.20): localized potential quadratic bound

Equation (2.20) resums exponentially decaying matrix elements into a local
quadratic form plus a field-independent volume remainder.  This module
connects that step to the repository Schur estimate and then combines it with
the equation-(2.22) large-field energy.

The terminal absorption theorem has the source shape

`interaction + gamma/2 * energyP
  <= alpha5/2 * localEnergy + residual`

provided the potential kernel costs `kernelRate`, the selected energy is
contained in the localization projector, and `kernelRate + gamma <= alpha5`.

Honest scope: the concrete Wilson-potential kernel must still be shown to
satisfy `ExpDecay` and the source row-summability constant.  This module proves
the analytic Schur/resummation implication, not those model-specific inputs.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- Schur's quadratic-form estimate localized to a finite carrier.  The field
is allowed to live on the ambient finite type but must vanish off `Y0`. -/
theorem cmp116Eq220_expDecay_quadratic_form_le_localized
    {V : Type*} [Fintype V] [DecidableEq V]
    (Y0 : Finset V)
    {d : V → V → ℝ} {amplitude kappa rowSum : ℝ}
    {K : V → V → ℝ}
    (hamplitude : 0 ≤ amplitude)
    (hsym : ∀ x y, d x y = d y x)
    (hdecay : ExpDecay d amplitude kappa K)
    (hrow : ∀ x, ∑ y, Real.exp (-kappa * d x y) ≤ rowSum)
    (u : V → ℝ) (hsupport : ∀ i, i ∉ Y0 → u i = 0) :
    |∑ x, ∑ y, u x * K x y * u y| ≤
      (amplitude * rowSum) * ∑ x ∈ Y0, u x ^ 2 := by
  have hschur := expDecay_quadratic_form_le
    hamplitude hsym hdecay hrow u
  have hsum : (∑ x, u x ^ 2) = ∑ x ∈ Y0, u x ^ 2 := by
    classical
    refine (Finset.sum_subset (Finset.subset_univ Y0) ?_).symm
    intro i hi hnot
    rw [hsupport i hnot]
    norm_num
  simpa [hsum] using hschur

/-- Equation-(2.20) consumer: a source pointwise potential estimate by the
absolute kernel quadratic is converted into the localized `l2` form with no
new analytic loss. -/
theorem cmp116Eq220_interaction_le_localized_of_expDecay
    {V : Type*} [Fintype V] [DecidableEq V]
    (Y0 : Finset V)
    {d : V → V → ℝ} {amplitude kappa rowSum interaction residual : ℝ}
    {K : V → V → ℝ}
    (hamplitude : 0 ≤ amplitude)
    (hsym : ∀ x y, d x y = d y x)
    (hdecay : ExpDecay d amplitude kappa K)
    (hrow : ∀ x, ∑ y, Real.exp (-kappa * d x y) ≤ rowSum)
    (u : V → ℝ) (hsupport : ∀ i, i ∉ Y0 → u i = 0)
    (hsource : interaction ≤
      (1 / 2 : ℝ) * |∑ x, ∑ y, u x * K x y * u y| + residual) :
    interaction ≤
      ((amplitude * rowSum) / 2) * (∑ x ∈ Y0, u x ^ 2) + residual := by
  have hquad := cmp116Eq220_expDecay_quadratic_form_le_localized
    Y0 hamplitude hsym hdecay hrow u hsupport
  nlinarith

/-- Scalar absorption used after equations (2.20)--(2.22).  It records the
exact coefficient budget needed to place both the potential quadratic and
the positive large-field energy inside `alpha5 * P_Z0`. -/
theorem cmp116Eq220_eq222_absorb_into_alpha5_localized
    {interaction kernelRate gamma alpha5 energyP localEnergy residual : ℝ}
    (hinteraction :
      interaction ≤ kernelRate / 2 * localEnergy + residual)
    (henergy : energyP ≤ localEnergy)
    (hgamma : 0 ≤ gamma)
    (hlocal : 0 ≤ localEnergy)
    (hbudget : kernelRate + gamma ≤ alpha5) :
    interaction + gamma / 2 * energyP ≤
      alpha5 / 2 * localEnergy + residual := by
  have hgammaEnergy : gamma / 2 * energyP ≤ gamma / 2 * localEnergy :=
    mul_le_mul_of_nonneg_left henergy (by positivity)
  have hcoefficient :
      kernelRate / 2 * localEnergy + gamma / 2 * localEnergy ≤
        alpha5 / 2 * localEnergy := by
    nlinarith
  linarith

end

end YangMills.RG
