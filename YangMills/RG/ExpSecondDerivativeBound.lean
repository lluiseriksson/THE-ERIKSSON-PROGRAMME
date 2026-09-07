/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogSecondDerivativeBound
import YangMills.RG.NoncommutativeExpLipschitz

/-!
# Explicit second derivative of the noncommutative exponential

The existing ordered-series estimate proves that the Fréchet derivative of
the noncommutative exponential is Lipschitz on every closed norm ball.  The
converse mean-value theorem therefore bounds the actual second iterated
derivative by the same factorial-series budget.

No Hessian estimate is assumed.
-/

namespace YangMills.RG

noncomputable section

open Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A]

/-- The actual second Fréchet derivative of the noncommutative exponential
is bounded by the explicit ordered-series budget on a closed ball. -/
theorem norm_iteratedFDeriv_two_exp_le_secondDerivativeBudget
    {r : ℝ} {Y : A} (hY : ‖Y‖ < r) :
    ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : A → A) Y‖ ≤
      expSecondDerivativeBudget r := by
  have hr0 : 0 ≤ r := (norm_nonneg Y).trans hY.le
  let C : NNReal :=
    ⟨expSecondDerivativeBudget r,
      expSecondDerivativeBudget_nonneg r hr0⟩
  have hlip :
      LipschitzOnWith C
        (fderiv ℝ (NormedSpace.exp : A → A))
        (Metric.closedBall 0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro X hX Z hZ
    have hXr : ‖X‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hX
    have hZr : ‖Z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hZ
    simpa [C, dist_eq_norm] using
      norm_fderiv_exp_sub_le_secondDerivativeBudget hXr hZr
  have hball : Metric.closedBall (0 : A) r ∈ 𝓝 Y :=
    Metric.closedBall_mem_nhds_of_mem (show
      Y ∈ Metric.ball (0 : A) r by
        simpa [Metric.mem_ball, dist_zero_right] using hY)
  have hderiv :
      ‖fderiv ℝ
          ((fderiv ℝ (NormedSpace.exp : A → A)) :
            A → A →L[ℝ] A) Y‖ ≤
        expSecondDerivativeBudget r := by
    simpa [C] using
      (norm_fderiv_le_of_lipschitzOn ℝ hball hlip)
  calc
    ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : A → A) Y‖ =
        ‖iteratedFDeriv ℝ 1
          (fderiv ℝ (NormedSpace.exp : A → A)) Y‖ := by
      simpa using
        (norm_iteratedFDeriv_fderiv
          (𝕜 := ℝ) (f := (NormedSpace.exp : A → A))
          (x := Y) (n := 1)).symm
    _ = ‖fderiv ℝ
        ((fderiv ℝ (NormedSpace.exp : A → A)) :
          A → A →L[ℝ] A) Y‖ := by
      rw [norm_iteratedFDeriv_one]
    _ ≤ expSecondDerivativeBudget r := hderiv

end

end YangMills.RG
