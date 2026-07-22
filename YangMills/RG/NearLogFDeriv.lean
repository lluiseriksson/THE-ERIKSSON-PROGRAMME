/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLog

/-!
# The Fréchet derivative of the local logarithm at the identity

The complete CMP98 block average is obtained by differentiating a nonlinear
logarithmic average.  This file closes the first analytic step of that
linearization: the Mercator map `nearLog`, written in deviation coordinates
around the identity, has Fréchet derivative equal to the identity at zero.

The proof is deliberately based on the already established sharp quadratic
remainder estimate

`‖nearLog Y - Y‖ ≤ ‖Y‖² / (1 - ‖Y‖)`.

Consequently the result does not assume termwise differentiation of the
infinite Mercator series, and it does not postulate any of the three
correction terms printed in CMP98 (124).
-/

namespace YangMills.RG

open Asymptotics

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The local logarithm differs from the identity by a quadratic big-O term
at the origin.  The constant `2` is valid on the ball `‖Y‖ < 1/2`. -/
theorem nearLog_sub_self_isBigO_norm_sq :
    (fun Y : 𝔸 => nearLog Y - Y) =O[nhds 0] (fun Y : 𝔸 => ‖Y‖ ^ 2) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : 𝔸) (by norm_num : (0 : ℝ) < 1 / 2)] with Y hY
  rw [mem_ball_zero_iff] at hY
  have hY1 : ‖Y‖ < 1 := by linarith
  have hdenom : 0 < 1 - ‖Y‖ := by linarith
  calc
    ‖nearLog Y - Y‖ ≤ ‖Y‖ ^ 2 / (1 - ‖Y‖) := norm_nearLog_sub_self_le hY1
    _ ≤ 2 * ‖Y‖ ^ 2 := by
      rw [div_le_iff₀ hdenom]
      nlinarith [sq_nonneg ‖Y‖]
    _ = 2 * ‖(‖Y‖ ^ 2 : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Y‖)]

/-- The quadratic remainder of `nearLog` is little-o of the input at zero. -/
theorem nearLog_sub_self_isLittleO_id :
    (fun Y : 𝔸 => nearLog Y - Y) =o[nhds 0] (fun Y : 𝔸 => Y) :=
  nearLog_sub_self_isBigO_norm_sq.trans_isLittleO
    (isLittleO_norm_pow_id one_lt_two)

/-- In deviation coordinates around the identity, the Mercator logarithm has
Fréchet derivative equal to the identity at zero. -/
theorem hasFDerivAt_nearLog_zero :
    HasFDerivAt (nearLog : 𝔸 → 𝔸) (ContinuousLinearMap.id ℝ 𝔸) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa using (nearLog_sub_self_isLittleO_id (𝔸 := 𝔸))

/-- Chain-rule interface for the actual use of the local logarithm: if an
algebra-valued deviation vanishes at the base point, applying `nearLog` does
not change its first derivative there. -/
theorem HasFDerivAt.nearLog_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → 𝔸} {F' : E →L[ℝ] 𝔸} {x : E}
    (hF : HasFDerivAt F F' x) (hzero : F x = 0) :
    HasFDerivAt (fun y => nearLog (F y)) F' x := by
  have hlog : HasFDerivAt (nearLog : 𝔸 → 𝔸)
      (ContinuousLinearMap.id ℝ 𝔸) (F x) := by
    simpa [hzero] using (hasFDerivAt_nearLog_zero (𝔸 := 𝔸))
  simpa using hlog.comp x hF

/-- The exact logarithmic chart used in CMP98 has identity derivative at the
trivial field: `X ↦ nearLog (exp X - 1)`.  This statement is valid in a
noncommutative Banach algebra because both constituent derivatives are taken
at zero. -/
theorem hasFDerivAt_nearLog_exp_sub_one_zero :
    HasFDerivAt
      (fun X : 𝔸 => nearLog (NormedSpace.exp X - 1))
      (ContinuousLinearMap.id ℝ 𝔸) 0 := by
  have hexp : HasFDerivAt
      (fun X : 𝔸 => NormedSpace.exp X - 1)
      (ContinuousLinearMap.id ℝ 𝔸) 0 := by
    simpa using
      (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).sub_const (1 : 𝔸)
  exact HasFDerivAt.nearLog_of_eq_zero hexp (by simp)

end

end YangMills.RG
