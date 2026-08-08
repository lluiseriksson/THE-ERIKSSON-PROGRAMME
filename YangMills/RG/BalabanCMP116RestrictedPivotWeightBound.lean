/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedMonomialLinearTelescope

/-!
# Uniform bound for one ordered restricted pivot weight

One ordered telescope term contains exactly one contour displacement and only
later full weakening factors.  Hence each pivot costs one radius and a stable
power of the weakening cap, with no powerset cardinality.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- Each ordered pivot weight is bounded by one contour radius and the
uniform weakening cap to the physical active carrier of the walk. -/
theorem norm_cmp116RestrictedOrderedPivotWeight_le
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (i : Fin n) :
    ‖cmp116RestrictedOrderedPivotWeight active carrier e z i‖ ≤
      radius * Rweak ^ active.card := by
  classical
  by_cases hactive : (e i : Delta) ∈ active
  · rw [cmp116RestrictedOrderedPivotWeight, if_pos hactive, norm_mul,
      norm_prod]
    let later :=
      (cmp116RestrictedActiveIndices carrier e active).filter
        (fun j => i < j)
    have hprod :
        ∏ j ∈ later, ‖1 + z j‖ ≤ ∏ _j ∈ later, Rweak := by
      exact Finset.prod_le_prod
        (fun j _ => norm_nonneg (1 + z j))
        (fun j _ => hcap j)
    have hindices :
        (cmp116RestrictedActiveIndices carrier e active).card ≤
          active.card := by
      apply Finset.card_le_card_of_injOn (fun j => (e j : Delta))
      · intro j hj
        exact
          (mem_cmp116RestrictedActiveIndices_iff carrier e active j).mp hj
      · intro j₁ _ j₂ _ hj
        exact e.injective (Subtype.ext hj)
    have hcard : later.card ≤ active.card := by
      calc
        later.card ≤
            (cmp116RestrictedActiveIndices carrier e active).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ active.card := hindices
    calc
      ‖z i‖ * ∏ j ∈ later, ‖1 + z j‖ ≤
          radius * ∏ _j ∈ later, Rweak :=
        mul_le_mul (hz i) hprod
          (Finset.prod_nonneg fun j _ => norm_nonneg (1 + z j))
          hradius
      _ = radius * Rweak ^ later.card := by simp
      _ ≤ radius * Rweak ^ active.card := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hRweak hcard) hradius
  · simp [cmp116RestrictedOrderedPivotWeight, hactive,
      mul_nonneg hradius (pow_nonneg (zero_le_one.trans hRweak) _)]

/-- Summing all possible ordered pivots costs exactly the localized contour
dimension, not the active-walk cardinality and not a powerset factor. -/
theorem sum_norm_cmp116RestrictedOrderedPivotWeight_le
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak) :
    ∑ i : Fin n,
        ‖cmp116RestrictedOrderedPivotWeight active carrier e z i‖ ≤
      (n : ℝ) * radius * Rweak ^ active.card := by
  calc
    ∑ i : Fin n,
        ‖cmp116RestrictedOrderedPivotWeight active carrier e z i‖ ≤
        ∑ _i : Fin n, radius * Rweak ^ active.card :=
      Finset.sum_le_sum fun i _ =>
        norm_cmp116RestrictedOrderedPivotWeight_le
          active carrier e z radius Rweak hradius hRweak hz hcap i
    _ = (n : ℝ) * radius * Rweak ^ active.card := by
      simp
      ring

end

end YangMills.RG
