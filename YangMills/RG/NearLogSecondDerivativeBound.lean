/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NoncommutativePowerLipschitz

/-!
# Explicit second derivative of the noncommutative Mercator logarithm

The derivative of `nearLog` is already known to be Lipschitz on every strict
closed sub-ball of its unit Mercator domain.  Applying the converse
mean-value inequality to that derivative and using the isometric currying
identity for iterated Fréchet derivatives produces a genuine second-jet
bound.
-/

namespace YangMills.RG

open Metric
open scoped Topology

noncomputable section

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

/-- On the interior of a strict Mercator sub-ball, the second iterated
Fréchet derivative is bounded by the explicit summed termwise budget. -/
theorem norm_iteratedFDeriv_two_nearLog_le_secondDerivativeBudget
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {Y : A} (hY : ‖Y‖ < r) :
    ‖iteratedFDeriv ℝ 2 (nearLog : A → A) Y‖ ≤
      nearLogSecondDerivativeBudget r := by
  let C : NNReal :=
    ⟨nearLogSecondDerivativeBudget r,
      nearLogSecondDerivativeBudget_nonneg r hr0⟩
  have hlip :
      LipschitzOnWith C
        (fderiv ℝ (nearLog : A → A))
        (Metric.closedBall 0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro X hX Z hZ
    have hXr : ‖X‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hX
    have hZr : ‖Z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hZ
    simpa [C, dist_eq_norm] using
      norm_fderiv_nearLog_sub_le_secondDerivativeBudget
        hr0 hr1 hXr hZr
  have hball : Metric.closedBall (0 : A) r ∈ 𝓝 Y :=
    Metric.closedBall_mem_nhds_of_mem (show
      Y ∈ Metric.ball (0 : A) r by
        simpa [Metric.mem_ball, dist_zero_right] using hY)
  have hderiv :
      ‖fderiv ℝ (fderiv ℝ (nearLog : A → A)) Y‖ ≤
        nearLogSecondDerivativeBudget r := by
    simpa [C] using
      (norm_fderiv_le_of_lipschitzOn ℝ hball hlip)
  calc
    ‖iteratedFDeriv ℝ 2 (nearLog : A → A) Y‖ =
        ‖iteratedFDeriv ℝ 1
          (fderiv ℝ (nearLog : A → A)) Y‖ := by
      simpa using
        (norm_iteratedFDeriv_fderiv
          (𝕜 := ℝ) (f := (nearLog : A → A)) (x := Y) (n := 1)).symm
    _ = ‖fderiv ℝ (fderiv ℝ (nearLog : A → A)) Y‖ := by
      rw [norm_iteratedFDeriv_one]
    _ ≤ nearLogSecondDerivativeBudget r := hderiv

end

end YangMills.RG
