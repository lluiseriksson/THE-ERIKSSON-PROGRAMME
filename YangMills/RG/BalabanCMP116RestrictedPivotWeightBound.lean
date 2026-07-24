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
uniform weakening cap to the total number of contour coordinates. -/
theorem norm_cmp116RestrictedOrderedPivotWeight_le
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) (radius Rweak : ℝ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hz : ∀ i, ‖z i‖ ≤ radius)
    (hcap : ∀ i, ‖1 + z i‖ ≤ Rweak)
    (i : Fin n) :
    ‖cmp116RestrictedOrderedPivotWeight active carrier e z i‖ ≤
      radius * Rweak ^ n := by
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
    have hcard : later.card ≤ n := by
      calc
        later.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ later)
        _ = n := by simp
    calc
      ‖z i‖ * ∏ j ∈ later, ‖1 + z j‖ ≤
          radius * ∏ _j ∈ later, Rweak :=
        mul_le_mul (hz i) hprod
          (Finset.prod_nonneg fun j _ => norm_nonneg (1 + z j))
          hradius
      _ = radius * Rweak ^ later.card := by simp
      _ ≤ radius * Rweak ^ n := by
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
      (n : ℝ) * radius * Rweak ^ n := by
  calc
    ∑ i : Fin n,
        ‖cmp116RestrictedOrderedPivotWeight active carrier e z i‖ ≤
        ∑ _i : Fin n, radius * Rweak ^ n :=
      Finset.sum_le_sum fun i _ =>
        norm_cmp116RestrictedOrderedPivotWeight_le
          active carrier e z radius Rweak hradius hRweak hz hcap i
    _ = (n : ℝ) * radius * Rweak ^ n := by
      simp
      ring

end

end YangMills.RG
