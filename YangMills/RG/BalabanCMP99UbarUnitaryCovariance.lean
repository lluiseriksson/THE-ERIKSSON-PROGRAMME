/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99UbarUnitary

/-!
# Gauge covariance of the unitary CMP99 background block

This file lifts the existing represented covariance theorem for CMP109
(0.12) to the canonical unitary-valued construction.  In particular, the
proof uses the explicit exponential/logarithm formula and never selects a
preimage in the unitary group.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [StarRing A] [ContinuousStar A] [StarModule ℝ A]

@[simp] theorem coe_toUnits_inv_eq_star (u : unitary A) :
    (↑((Unitary.toUnits u)⁻¹) : A) = star (u : A) := by
  rw [Unitary.val_inv_toUnits_apply, ← Unitary.star_eq_inv u,
    Unitary.coe_star]

/-- Conjugating a group element and then subtracting one is the same as
conjugating its deviation from one. -/
theorem unitary_conj_sub_one (u : unitary A) (D : A) :
    (u : A) * D * star (u : A) - 1 =
      (u : A) * (D - 1) * star (u : A) := by
  rw [mul_sub, sub_mul, mul_one]
  simp [mul_assoc]

/-- Skew-adjointness of a Mercator coordinate is preserved by unitary
conjugation. -/
theorem nearLog_unitary_conj_sub_one_mem_skewAdjoint (u : unitary A) (D : A)
    (hD : ‖D - 1‖ < 1)
    (hlog : nearLog (D - 1) ∈ skewAdjoint A) :
    nearLog ((u : A) * D * star (u : A) - 1) ∈ skewAdjoint A := by
  rw [unitary_conj_sub_one]
  have hconj := nearLog_conj (Unitary.toUnits u) hD
  rw [Unitary.val_toUnits_apply, coe_toUnits_inv_eq_star] at hconj
  rw [hconj]
  exact skewAdjoint.conjugate hlog (u : A)

/-- The literal CMP99 exponent conjugates without loss or choice. -/
theorem cmp99UbarExponent_conj {ι : Type*} (u : unitary A) (s : Finset ι)
    (w : ι → ℝ) (D : ι → A) (hD : ∀ i ∈ s, ‖D i - 1‖ < 1) :
    cmp99UbarExponent s w (fun i => (u : A) * D i * star (u : A)) =
      (u : A) * cmp99UbarExponent s w D * star (u : A) := by
  have hconj := nearLog_sum_smul_conj (Unitary.toUnits u) s w
    (fun i => D i - 1) hD
  rw [Unitary.val_toUnits_apply, coe_toUnits_inv_eq_star] at hconj
  simpa only [cmp99UbarExponent, unitary_conj_sub_one] using hconj

/-- The canonical unitary CMP99 block obeys the exact gauge-conjugation law.
The proof is equality in the unitary group, not merely equality of ambient
representatives. -/
theorem cmp99UbarUnitaryBlock_conj {ι : Type*} (u : unitary A) (s : Finset ι)
    (w : ι → ℝ) (D : ι → A) (hD : ∀ i ∈ s, ‖D i - 1‖ < 1)
    (hlog : ∀ i ∈ s, nearLog (D i - 1) ∈ skewAdjoint A)
    (coarse : unitary A) :
    cmp99UbarUnitaryBlock s w (fun i => (u : A) * D i * star (u : A))
        (fun i hi => nearLog_unitary_conj_sub_one_mem_skewAdjoint
          u (D i) (hD i hi) (hlog i hi))
        (u * coarse * star u) =
      u * cmp99UbarUnitaryBlock s w D hlog coarse * star u := by
  apply Subtype.ext
  change
    NormedSpace.exp
        (cmp99UbarExponent s w (fun i => (u : A) * D i * star (u : A))) *
        ((u : A) * (coarse : A) * star (u : A)) =
      (u : A) *
        (NormedSpace.exp (cmp99UbarExponent s w D) * (coarse : A)) *
        star (u : A)
  rw [cmp99UbarExponent_conj u s w D hD]
  have hexp := NormedSpace.exp_units_conj (Unitary.toUnits u)
    (cmp99UbarExponent s w D)
  rw [Unitary.val_toUnits_apply, coe_toUnits_inv_eq_star] at hexp
  rw [hexp]
  simp only [mul_assoc]
  rw [← mul_assoc (star (u : A)) (u : A)
    ((coarse : A) * star (u : A))]
  rw [show star (u : A) * (u : A) = 1 from Unitary.coe_star_mul_self u]
  simp

end

end YangMills.RG
