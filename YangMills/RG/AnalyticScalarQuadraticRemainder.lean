/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Quadratic Taylor remainder for an analytic real curve

This is the small reusable analytic lemma needed by CMP98 (123).  It is a
direct consequence of Mathlib's formal-power-series Taylor estimate: an
analytic Banach-valued real curve differs from its value and first derivative
by `O(t²)`.
-/

namespace YangMills.RG

open Asymptotics

/-- An analytic Banach-valued real curve has a quadratic first-order Taylor
remainder at the origin. -/
theorem AnalyticAt.isBigO_sub_value_sub_deriv_smul_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : AnalyticAt ℝ f 0) :
    (fun t : ℝ => f t - f 0 - t • deriv f 0) =O[nhds 0]
      (fun t : ℝ => t ^ 2) := by
  rcases hf with ⟨p, hp⟩
  have h := hp.isBigO_sub_partialSum_pow 2
  have hp1 : p 1 (fun _ => (1 : ℝ)) = deriv f 0 :=
    hp.hasDerivAt.deriv.symm
  refine h.congr' ?_ (Filter.Eventually.of_forall fun t => by
    simp [Real.norm_eq_abs, sq_abs])
  filter_upwards [] with t
  simp only [zero_add]
  rw [FormalMultilinearSeries.partialSum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have hp0t : p 0 (fun _ : Fin 0 => t) = f 0 := hp.coeff_zero _
  rw [hp0t, zero_add]
  have hlin : p 1 (fun _ : Fin 1 => t) = t • deriv f 0 := by
    have hmap := (p 1).map_smul_univ
      (fun _ : Fin 1 => t) (fun _ : Fin 1 => (1 : ℝ))
    simpa [hp1] using hmap
  rw [hlin]
  abel

end YangMills.RG
