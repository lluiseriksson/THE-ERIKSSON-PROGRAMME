/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# A local second-jet bound from derivative Lipschitz control

This is the converse mean-value estimate applied to the derivative map.
Only a germ of the Lipschitz comparison at the base point is required.
-/

namespace YangMills.RG

open scoped Topology

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the Fréchet derivative of `f` is locally `C`-Lipschitz at `x`,
then the second iterated Fréchet derivative at `x` has norm at most `C`.
No global smoothness hypothesis is needed. -/
theorem norm_iteratedFDeriv_two_le_of_eventually_fderiv_lipschitz
    (f : E → F) (x : E) {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ᶠ y in 𝓝 x,
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y - x‖) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ C := by
  rw [show 2 = 1 + 1 by norm_num, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_one]
  exact norm_fderiv_le_of_lip' ℝ hC hlip

end

end YangMills.RG
