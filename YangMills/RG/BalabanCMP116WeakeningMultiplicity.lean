/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexWeakenedRandomWalkSeries

/-!
# Multiplicity-aware complex weakening monomials

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations are not yet compiler-verified.

The square-free monomial attached to one walk carrier is sufficient for one
generalized random-walk propagator.  Products of independently weakened
physical factors need more information: overlapping carriers contribute
repeated powers of the same weakening coordinate.  This module records those
multiplicities as a finitely supported natural-valued function.

The construction is exact algebra.  In particular, the product of factors
`m_i(s) - 1` is expanded over omitted factors, and every surviving product is
represented by the sum of its carrier multiplicities.  No disjointness of
carriers and no analytic estimate is assumed.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v

/-- One occurrence of every coordinate in a finite active carrier. -/
def cmp116WeakeningCarrierMultiplicity
    {Delta : Type u} [DecidableEq Delta]
    (active : Finset Delta) : Delta →₀ ℕ :=
  ∑ d ∈ active, Finsupp.single d 1

/-- Complex monomial with the exponent of every coordinate retained. -/
def cmp116ComplexWeakeningMultiplicityMonomial
    {Delta : Type u}
    (multiplicity : Delta →₀ ℕ) (sigma : Delta → ℂ) : ℂ :=
  multiplicity.prod fun d n => sigma d ^ n

@[simp] theorem cmp116ComplexWeakeningMultiplicityMonomial_zero
    {Delta : Type u} (sigma : Delta → ℂ) :
    cmp116ComplexWeakeningMultiplicityMonomial 0 sigma = 1 := by
  rfl

/-- Addition of multiplicities is multiplication of the corresponding
complex monomials. -/
theorem cmp116ComplexWeakeningMultiplicityMonomial_add
    {Delta : Type u}
    (left right : Delta →₀ ℕ) (sigma : Delta → ℂ) :
    cmp116ComplexWeakeningMultiplicityMonomial (left + right) sigma =
      cmp116ComplexWeakeningMultiplicityMonomial left sigma *
        cmp116ComplexWeakeningMultiplicityMonomial right sigma := by
  exact Finsupp.prod_add_index'
    (fun d => by simp [cmp116ComplexWeakeningMultiplicityMonomial])
    (fun d n₁ n₂ => by simp [cmp116ComplexWeakeningMultiplicityMonomial,
      pow_add])

@[simp] theorem cmp116ComplexWeakeningMultiplicityMonomial_single
    {Delta : Type u} (d : Delta) (n : ℕ) (sigma : Delta → ℂ) :
    cmp116ComplexWeakeningMultiplicityMonomial
        (Finsupp.single d n) sigma =
      sigma d ^ n := by
  simpa [cmp116ComplexWeakeningMultiplicityMonomial] using
    (Finsupp.prod_single_index
      (a := d) (b := n) (h := fun x m => sigma x ^ m) (by simp))

theorem cmp116WeakeningCarrierMultiplicity_insert
    {Delta : Type u} [DecidableEq Delta]
    (d : Delta) (active : Finset Delta) (hd : d ∉ active) :
    cmp116WeakeningCarrierMultiplicity (insert d active) =
      Finsupp.single d 1 + cmp116WeakeningCarrierMultiplicity active := by
  simp [cmp116WeakeningCarrierMultiplicity, Finset.sum_insert, hd]

/-- The old square-free monomial is the multiplicity monomial of the
carrier indicator. -/
theorem cmp116ComplexWeakeningMonomial_eq_multiplicityMonomial
    {Delta : Type u} [DecidableEq Delta]
    (active : Finset Delta) (sigma : Delta → ℂ) :
    cmp116ComplexWeakeningMonomial active sigma =
      cmp116ComplexWeakeningMultiplicityMonomial
        (cmp116WeakeningCarrierMultiplicity active) sigma := by
  induction active using Finset.induction_on with
  | empty =>
      simp [cmp116ComplexWeakeningMonomial,
        cmp116WeakeningCarrierMultiplicity]
  | @insert d active hd ih =>
      calc
        cmp116ComplexWeakeningMonomial (insert d active) sigma =
            sigma d * cmp116ComplexWeakeningMonomial active sigma := by
          simp [cmp116ComplexWeakeningMonomial, Finset.prod_insert, hd]
        _ = sigma d *
            cmp116ComplexWeakeningMultiplicityMonomial
              (cmp116WeakeningCarrierMultiplicity active) sigma :=
          congrArg (fun z => sigma d * z) ih
        _ = cmp116ComplexWeakeningMultiplicityMonomial
              (Finsupp.single d 1) sigma *
            cmp116ComplexWeakeningMultiplicityMonomial
              (cmp116WeakeningCarrierMultiplicity active) sigma := by
          simp
        _ = cmp116ComplexWeakeningMultiplicityMonomial
              (Finsupp.single d 1 +
                cmp116WeakeningCarrierMultiplicity active) sigma :=
          (cmp116ComplexWeakeningMultiplicityMonomial_add
            (Finsupp.single d 1)
            (cmp116WeakeningCarrierMultiplicity active) sigma).symm
        _ = cmp116ComplexWeakeningMultiplicityMonomial
              (cmp116WeakeningCarrierMultiplicity (insert d active)) sigma := by
          rw [cmp116WeakeningCarrierMultiplicity_insert d active hd]

/-- Total multiplicity contributed by a finite family of carriers. -/
def cmp116WeakeningFamilyMultiplicity
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (indices : Finset Index) (active : Index → Finset Delta) : Delta →₀ ℕ :=
  ∑ i ∈ indices, cmp116WeakeningCarrierMultiplicity (active i)

theorem cmp116WeakeningFamilyMultiplicity_insert
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (i : Index) (indices : Finset Index) (hi : i ∉ indices)
    (active : Index → Finset Delta) :
    cmp116WeakeningFamilyMultiplicity (insert i indices) active =
      cmp116WeakeningCarrierMultiplicity (active i) +
        cmp116WeakeningFamilyMultiplicity indices active := by
  simp [cmp116WeakeningFamilyMultiplicity, Finset.sum_insert, hi]

/-- A product of square-free carrier monomials is the single monomial whose
exponents count every occurrence, including overlaps between carriers. -/
theorem prod_cmp116ComplexWeakeningMonomial_eq_multiplicityMonomial
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (indices : Finset Index) (active : Index → Finset Delta)
    (sigma : Delta → ℂ) :
    (∏ i ∈ indices, cmp116ComplexWeakeningMonomial (active i) sigma) =
      cmp116ComplexWeakeningMultiplicityMonomial
        (cmp116WeakeningFamilyMultiplicity indices active) sigma := by
  induction indices using Finset.induction_on with
  | empty =>
      simp [cmp116WeakeningFamilyMultiplicity]
  | @insert i indices hi ih =>
      rw [Finset.prod_insert hi,
        cmp116WeakeningFamilyMultiplicity_insert i indices hi,
        cmp116ComplexWeakeningMultiplicityMonomial_add,
        ← cmp116ComplexWeakeningMonomial_eq_multiplicityMonomial]
      exact congrArg
        (fun z => cmp116ComplexWeakeningMonomial (active i) sigma * z) ih

/-- Exact powerset expansion of a product of weakened differences.  A set
`omitted` selects the factors contributing `-1`; all other factors retain
their carrier, and carrier overlaps are recorded additively. -/
theorem prod_cmp116ComplexWeakeningMonomial_sub_one_eq
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (indices : Finset Index) (active : Index → Finset Delta)
    (sigma : Delta → ℂ) :
    (∏ i ∈ indices,
        (cmp116ComplexWeakeningMonomial (active i) sigma - 1)) =
      ∑ omitted ∈ indices.powerset,
        (-1 : ℂ) ^ omitted.card *
          cmp116ComplexWeakeningMultiplicityMonomial
            (cmp116WeakeningFamilyMultiplicity
              (indices \ omitted) active) sigma := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro omitted homitted
  rw [prod_cmp116ComplexWeakeningMonomial_eq_multiplicityMonomial]
  simp

/-- Multiplying a head monomial by a family product adds the head carrier to
the full multiplicity instead of silently replacing it by a union. -/
theorem cmp116ComplexWeakeningMonomial_mul_prod_eq_multiplicityMonomial
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (head : Finset Delta) (indices : Finset Index)
    (active : Index → Finset Delta) (sigma : Delta → ℂ) :
    cmp116ComplexWeakeningMonomial head sigma *
        ∏ i ∈ indices, cmp116ComplexWeakeningMonomial (active i) sigma =
      cmp116ComplexWeakeningMultiplicityMonomial
        (cmp116WeakeningCarrierMultiplicity head +
          cmp116WeakeningFamilyMultiplicity indices active) sigma := by
  rw [cmp116ComplexWeakeningMonomial_eq_multiplicityMonomial,
    prod_cmp116ComplexWeakeningMonomial_eq_multiplicityMonomial,
    ← cmp116ComplexWeakeningMultiplicityMonomial_add]

end

end YangMills.RG
