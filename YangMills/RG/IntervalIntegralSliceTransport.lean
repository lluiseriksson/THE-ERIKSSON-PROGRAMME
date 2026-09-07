/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Transport of interval-integral slice equalities

This module was compiler-verified from exact source checkpoint
`3f434e990cdb8a0b985bf1d4cb91a999e53eb536` by cold GitHub Actions run
`31291655520`.  Restore and save of `.lake/build` were both skipped; the
focal and audit exited zero, and the audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`.

This file isolates the Fubini step needed to iterate the physical CMP89
one-coordinate contour displacement.  If two integrable functions have the
same interval integral in the first variable for every value of the remaining
variables, then their full iterated integrals agree.  The conclusion is not a
formal congruence: integrability of both uncurried functions is the
load-bearing hypothesis that permits the interval integral to cross the
remaining measure.

No physical periodicity, contour estimate, `B0`, or window-15 conclusion is
introduced here.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Lift an equality of interval integrals on every slice to the full
iterated integral.  This is the Bochner/Fubini transport needed when the
coordinate being contour-shifted is outside the remaining integrals. -/
theorem intervalIntegral_integral_eq_of_slice_intervalIntegral_eq
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [SFinite μ] {a b : ℝ} {f g : ℝ → α → E}
    (hf : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc a b)).prod μ))
    (hg : Integrable (Function.uncurry g)
      ((volume.restrict (Set.uIoc a b)).prod μ))
    (hfg : ∀ y, (∫ x in a..b, f x y) = ∫ x in a..b, g x y) :
    (∫ x in a..b, ∫ y, f x y ∂μ) =
      ∫ x in a..b, ∫ y, g x y ∂μ := by
  rw [intervalIntegral_integral_swap hf,
    intervalIntegral_integral_swap hg]
  exact integral_congr_ae (Filter.Eventually.of_forall hfg)

end

end YangMills.RG
