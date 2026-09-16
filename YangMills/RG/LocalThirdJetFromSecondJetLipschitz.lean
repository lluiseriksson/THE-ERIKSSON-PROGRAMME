/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# A local third-jet bound from second-jet Lipschitz control

This is the converse mean-value estimate applied to the actual second
iterated Fréchet derivative.  Only a germ of the Lipschitz comparison at
the base point is required.
-/

namespace YangMills.RG

open scoped Topology

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the second iterated Fréchet derivative of `f` is locally
`C`-Lipschitz at `x`, then the third iterated Fréchet derivative at `x`
has norm at most `C`.  No global smoothness hypothesis is needed. -/
theorem norm_iteratedFDeriv_three_le_of_eventually_secondJet_lipschitz
    (f : E → F) (x : E) {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ᶠ y in 𝓝 x,
      ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤
        C * ‖y - x‖) :
    ‖iteratedFDeriv ℝ 3 f x‖ ≤ C := by
  rw [show 3 = 2 + 1 by norm_num, ← norm_fderiv_iteratedFDeriv]
  exact norm_fderiv_le_of_lip' ℝ hC hlip

end

end YangMills.RG
