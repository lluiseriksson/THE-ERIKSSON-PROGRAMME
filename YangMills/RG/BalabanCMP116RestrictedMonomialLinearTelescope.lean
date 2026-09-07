/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceRestrictedShiftedComplexContour

/-!
# Linear ordered telescope for a restricted weakening monomial

The nonempty-powerset expansion of a weakening defect has exponentially many
terms.  For determinant localization the useful exact identity is instead an
ordered telescope with one summand per physical contour coordinate.

The coordinate equivalence supplied by the Cauchy contour fixes an order on
the carrier.  The resulting formula assigns every monomial defect to its
first responsible coordinate in that order and contains exactly
`carrier.card` possible pivots.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- Cauchy-coordinate indices whose physical carrier point belongs to the
active weakening set. -/
def cmp116RestrictedActiveIndices
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (active : Finset Delta) : Finset (Fin n) :=
  Finset.univ.filter fun i => (e i : Delta) ∈ active

/-- Contribution assigned to one ordered physical contour coordinate.  It is
zero unless that coordinate belongs to the active weakening carrier. -/
def cmp116RestrictedOrderedPivotWeight
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) (i : Fin n) : ℂ :=
  if (e i : Delta) ∈ active then
    z i *
      ∏ j ∈
        (cmp116RestrictedActiveIndices carrier e active).filter
          (fun j => i < j),
        (1 + z j)
  else 0

theorem mem_active_of_cmp116RestrictedOrderedPivotWeight_ne_zero
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) (i : Fin n)
    (hweight :
      cmp116RestrictedOrderedPivotWeight active carrier e z i ≠ 0) :
    (e i : Delta) ∈ active := by
  by_contra hactive
  simp [cmp116RestrictedOrderedPivotWeight, hactive] at hweight

@[simp]
theorem mem_cmp116RestrictedActiveIndices_iff
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (active : Finset Delta) (i : Fin n) :
    i ∈ cmp116RestrictedActiveIndices carrier e active ↔
      (e i : Delta) ∈ active := by
  simp [cmp116RestrictedActiveIndices]

/-- The restricted physical monomial is exactly the product over its active
Cauchy-coordinate indices. -/
theorem cmp116ComplexWeakeningMonomial_restricted_eq_prod_activeIndices
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) :
    cmp116ComplexWeakeningMonomial active
        (cmp116SourceRestrictedShiftedCoupling carrier e z) =
      ∏ i ∈ cmp116RestrictedActiveIndices carrier e active, (1 + z i) := by
  classical
  rw [cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling]
  unfold cmp116ComplexWeakeningMonomial
  symm
  apply Finset.prod_bij
      (fun i _ => (e i : Delta))
  · intro i hi
    rw [Finset.mem_inter]
    exact
      ⟨(mem_cmp116RestrictedActiveIndices_iff
          carrier e active i).mp hi, (e i).2⟩
  · intro i₁ hi₁ i₂ hi₂ heq
    apply e.injective
    exact Subtype.ext heq
  · intro d hd
    have hdActive : d ∈ active := (Finset.mem_inter.mp hd).1
    have hdCarrier : d ∈ carrier := (Finset.mem_inter.mp hd).2
    let i : Fin n := e.symm ⟨d, hdCarrier⟩
    refine ⟨i, ?_, ?_⟩
    · exact
        (mem_cmp116RestrictedActiveIndices_iff
          carrier e active i).mpr <| by
            simpa [i] using hdActive
    · simp [i]
  · intro i hi
    simp [cmp116SourceRestrictedShiftedCoupling]

/-- Exact linear telescope of the restricted monomial defect.  Unlike the
powerset expansion, this formula has one term per active contour coordinate.
The factors with larger coordinate index remain at their shifted values. -/
theorem cmp116ComplexWeakeningMonomial_restricted_sub_one_eq_orderedSum
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) :
    cmp116ComplexWeakeningMonomial active
          (cmp116SourceRestrictedShiftedCoupling carrier e z) - 1 =
      ∑ i ∈ cmp116RestrictedActiveIndices carrier e active,
        z i *
          ∏ j ∈
            (cmp116RestrictedActiveIndices carrier e active).filter
              (fun j => i < j),
            (1 + z j) := by
  classical
  let s := cmp116RestrictedActiveIndices carrier e active
  have htel :
      (1 : ℂ) =
        (∏ i ∈ s, (1 + z i)) -
          ∑ i ∈ s,
            z i * ∏ j ∈ s.filter (fun j => i < j), (1 + z j) := by
    simpa [s] using
      (Finset.prod_sub_ordered s (fun i => 1 + z i) z)
  rw [cmp116ComplexWeakeningMonomial_restricted_eq_prod_activeIndices]
  dsimp [s] at htel
  linear_combination -htel

/-- Fintype form of the linear telescope.  It is tailored to moving the
coordinate sum outside the finite walk sum: every inactive coordinate
contributes exactly zero. -/
theorem cmp116ComplexWeakeningMonomial_restricted_sub_one_eq_sum_pivotWeight
    {n : ℕ} {Delta : Type*} [DecidableEq Delta]
    (active carrier : Finset Delta) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) :
    cmp116ComplexWeakeningMonomial active
          (cmp116SourceRestrictedShiftedCoupling carrier e z) - 1 =
      ∑ i : Fin n,
        cmp116RestrictedOrderedPivotWeight active carrier e z i := by
  rw [cmp116ComplexWeakeningMonomial_restricted_sub_one_eq_orderedSum]
  classical
  change
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => (e i : Delta) ∈ active),
      z i *
        ∏ j ∈
          (Finset.univ.filter
            (fun j : Fin n => (e j : Delta) ∈ active)).filter
              (fun j => i < j),
          (1 + z j)) =
      ∑ i ∈ Finset.univ,
        if (e i : Delta) ∈ active then
          z i *
            ∏ j ∈
              (Finset.univ.filter
                (fun j : Fin n => (e j : Delta) ∈ active)).filter
                  (fun j => i < j),
              (1 + z j)
        else 0
  rw [Finset.sum_filter]

end

end YangMills.RG
