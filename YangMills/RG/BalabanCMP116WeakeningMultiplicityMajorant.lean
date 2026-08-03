/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116WeakeningMultiplicity

/-!
# Radial majorants for weakening multiplicities

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its results have not yet been verified by the Lean compiler.

Products of independently weakened physical factors need the total number of
coordinate occurrences, not merely the cardinality of their union.  This file
defines that total degree for a finitely supported multiplicity and proves the
corresponding radial monomial bound.

This is finite algebra only.  In particular, it does not assert summability of
the powerset-expanded CMP99 series and it does not supply the source-specific
short/long-walk estimate needed for that summability.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v w

/-- Total number of weakening-coordinate occurrences, retaining repetitions
caused by overlapping carriers. -/
def cmp116WeakeningMultiplicityDegree
    {Delta : Type u} (multiplicity : Delta →₀ ℕ) : ℕ :=
  multiplicity.sum fun _ n => n

@[simp] theorem cmp116WeakeningMultiplicityDegree_zero
    {Delta : Type u} :
    cmp116WeakeningMultiplicityDegree (0 : Delta →₀ ℕ) = 0 := by
  rfl

/-- Adding multiplicities adds their total degrees. -/
theorem cmp116WeakeningMultiplicityDegree_add
    {Delta : Type u} (left right : Delta →₀ ℕ) :
    cmp116WeakeningMultiplicityDegree (left + right) =
      cmp116WeakeningMultiplicityDegree left +
        cmp116WeakeningMultiplicityDegree right := by
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem cmp116WeakeningMultiplicityDegree_single
    {Delta : Type u} (d : Delta) (n : ℕ) :
    cmp116WeakeningMultiplicityDegree (Finsupp.single d n) = n := by
  classical
  simp [cmp116WeakeningMultiplicityDegree]

/-- A square-free carrier has degree equal to its cardinality. -/
theorem cmp116WeakeningMultiplicityDegree_carrier
    {Delta : Type u} [DecidableEq Delta] (active : Finset Delta) :
    cmp116WeakeningMultiplicityDegree
        (cmp116WeakeningCarrierMultiplicity active) = active.card := by
  induction active using Finset.induction_on with
  | empty =>
      simp [cmp116WeakeningCarrierMultiplicity]
  | @insert d active hd ih =>
      rw [cmp116WeakeningCarrierMultiplicity_insert d active hd,
        cmp116WeakeningMultiplicityDegree_add,
        cmp116WeakeningMultiplicityDegree_single, ih,
        Finset.card_insert_of_notMem hd]
      rfl

/-- The degree of a finite family multiplicity is the sum of the carrier
cardinalities, even when the carriers overlap. -/
theorem cmp116WeakeningMultiplicityDegree_family
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (indices : Finset Index) (active : Index → Finset Delta) :
    cmp116WeakeningMultiplicityDegree
        (cmp116WeakeningFamilyMultiplicity indices active) =
      ∑ i ∈ indices, (active i).card := by
  induction indices using Finset.induction_on with
  | empty =>
      simp [cmp116WeakeningFamilyMultiplicity]
  | @insert i indices hi ih =>
      rw [cmp116WeakeningFamilyMultiplicity_insert i indices hi,
        cmp116WeakeningMultiplicityDegree_add,
        cmp116WeakeningMultiplicityDegree_carrier, ih,
        Finset.sum_insert hi]

/-- A uniform coordinate norm cap controls a multiplicity monomial by the
radial power whose exponent is the total multiplicity degree. -/
theorem norm_cmp116ComplexWeakeningMultiplicityMonomial_le_pow_degree
    {Delta : Type u}
    (multiplicity : Delta →₀ ℕ) (sigma : Delta → ℂ) (R : ℝ)
    (hsigma : ∀ d ∈ multiplicity.support, ‖sigma d‖ ≤ R) :
    ‖cmp116ComplexWeakeningMultiplicityMonomial multiplicity sigma‖ ≤
      R ^ cmp116WeakeningMultiplicityDegree multiplicity := by
  rw [cmp116ComplexWeakeningMultiplicityMonomial, Finsupp.prod, norm_prod]
  calc
    ∏ d ∈ multiplicity.support, ‖sigma d ^ multiplicity d‖ ≤
        ∏ d ∈ multiplicity.support, R ^ multiplicity d := by
      exact Finset.prod_le_prod
        (fun d _ => norm_nonneg (sigma d ^ multiplicity d))
        (fun d hd => by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg (sigma d)) (hsigma d hd) _)
    _ = R ^ ∑ d ∈ multiplicity.support, multiplicity d :=
      Finset.prod_pow_eq_pow_sum multiplicity.support
        (fun d => multiplicity d) R
    _ = R ^ cmp116WeakeningMultiplicityDegree multiplicity := by
      rfl

/-- The same total-degree power controls one multiplicity-weighted term. -/
theorem norm_cmp116ComplexWeakeningMultiplicityTerm_le_radialMajorant
    {Delta : Type u} {E : Type w}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (multiplicity : Delta →₀ ℕ) (term : E)
    (sigma : Delta → ℂ) (R : ℝ)
    (hsigma : ∀ d ∈ multiplicity.support, ‖sigma d‖ ≤ R) :
    ‖cmp116ComplexWeakeningMultiplicityMonomial multiplicity sigma • term‖ ≤
      R ^ cmp116WeakeningMultiplicityDegree multiplicity * ‖term‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_cmp116ComplexWeakeningMultiplicityMonomial_le_pow_degree
      multiplicity sigma R hsigma)
    (norm_nonneg term)

end

end YangMills.RG
