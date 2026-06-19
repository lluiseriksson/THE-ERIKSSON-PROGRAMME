/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Uniform activity bounds pass to pointwise limits

This tiny bridge packages a common decoupling/regularisation pattern: if a
family of activities has a profile bound uniformly in the regulator and
converges pointwise, then the limiting activity obeys the same profile.

It is intentionally abstract.  It does not prove any supersymmetric
decoupling, heavy-fermion expansion, or Yang--Mills activity estimate; it only
records the topological consumer once those estimates are supplied.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

/-- A pointwise limit of uniformly profile-bounded complex activities obeys the
same profile bound. -/
theorem activity_profile_bound_of_tendsto
    {ι : Type*} (z : ℕ → ι → ℂ) (zLim : ι → ℂ) (profile : ι → ℝ)
    (hbound : ∀ n X, ‖z n X‖ ≤ profile X)
    (hlim : ∀ X, Filter.Tendsto (fun n : ℕ => z n X) Filter.atTop (nhds (zLim X))) :
    ∀ X, ‖zLim X‖ ≤ profile X := by
  intro X
  exact le_of_tendsto' ((hlim X).norm) (fun n => hbound n X)

end YangMills.RG
