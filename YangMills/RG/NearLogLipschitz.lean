/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogLocalInverse
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A quantitative Lipschitz bound for the noncommutative Mercator logarithm

The derivative series already constructed for `nearLog` gives a uniform
operator-norm majorant on every closed ball of radius `r < 1`.  The Banach
space mean-value inequality then supplies a genuine two-point estimate.
This avoids introducing a supplied second-derivative constant when CMP98
moves from its small background to a nearby physical contour.
-/

namespace YangMills.RG

open Metric Set

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
  [NormOneClass 𝔸]

/-- Summed operator-norm budget for the Mercator derivative on the closed
ball of radius `r`. -/
def nearLogDerivativeBudget (r : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * r ^ n.pred

theorem nearLogDerivativeBudget_nonneg (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ nearLogDerivativeBudget r := by
  unfold nearLogDerivativeBudget
  exact tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hr _)

/-- The exact Fréchet derivative of `nearLog` is uniformly bounded by the
summed Mercator budget on a smaller closed ball. -/
theorem norm_fderiv_nearLog_le_derivativeBudget
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {Y : 𝔸} (hY : ‖Y‖ ≤ r) :
    ‖fderiv ℝ (nearLog : 𝔸 → 𝔸) Y‖ ≤ nearLogDerivativeBudget r := by
  have hYlt : ‖Y‖ < 1 := hY.trans_lt hr1
  have hder := hasFDerivAt_nearLog_of_norm_lt_one hYlt
  have hmajor : Summable (fun n : ℕ => (n : ℝ) * r ^ n.pred) :=
    summable_natCast_mul_pow_pred hr0 hr1
  have htermsNorm : Summable (fun n : ℕ => ‖nearLogTermFDeriv Y n‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => (norm_nearLogTermFDeriv_le Y n).trans <| by gcongr)
  rw [hder.fderiv]
  calc
    ‖∑' n : ℕ, nearLogTermFDeriv Y n‖
        ≤ ∑' n : ℕ, ‖nearLogTermFDeriv Y n‖ :=
          norm_tsum_le_tsum_norm htermsNorm
    _ ≤ ∑' n : ℕ, (n : ℝ) * r ^ n.pred := by
      exact htermsNorm.tsum_le_tsum
        (fun n => (norm_nearLogTermFDeriv_le Y n).trans <| by
          gcongr)
        hmajor
    _ = nearLogDerivativeBudget r := rfl

/-- Quantitative two-point Mercator estimate on a closed sub-ball of its
domain. -/
theorem norm_nearLog_sub_nearLog_le
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {Y Z : 𝔸} (hY : ‖Y‖ ≤ r) (hZ : ‖Z‖ ≤ r) :
    ‖nearLog Y - nearLog Z‖ ≤
      nearLogDerivativeBudget r * ‖Y - Z‖ := by
  let s : Set 𝔸 := Metric.closedBall (0 : 𝔸) r
  have hYs : Y ∈ s := by simpa [s, mem_closedBall_zero_iff] using hY
  have hZs : Z ∈ s := by simpa [s, mem_closedBall_zero_iff] using hZ
  have hdiff : ∀ W ∈ s, DifferentiableAt ℝ (nearLog : 𝔸 → 𝔸) W := by
    intro W hW
    have hWr : ‖W‖ ≤ r := by
      simpa [s, mem_closedBall_zero_iff] using hW
    exact (hasFDerivAt_nearLog_of_norm_lt_one (hWr.trans_lt hr1)).differentiableAt
  have hbound : ∀ W ∈ s,
      ‖fderiv ℝ (nearLog : 𝔸 → 𝔸) W‖ ≤ nearLogDerivativeBudget r := by
    intro W hW
    apply norm_fderiv_nearLog_le_derivativeBudget hr0 hr1
    simpa [s, mem_closedBall_zero_iff] using hW
  exact (convex_closedBall (0 : 𝔸) r).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound hZs hYs

end

end YangMills.RG
