/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116WeakeningMultiplicityMajorant

/-!
# Powerset majorants for weakening multiplicities

The exact expansion of a product of weakened differences has one finite term
for every omitted subset.  This module records the honest finite cost of that
expansion: the radial exponent is the total carrier multiplicity, while the
number of summands is `2 ^ indices.card`.

No infinite sum is rearranged here.  In particular, the factor `2 ^ n` is not
silently absorbed into a physical contour ratio; that is a subsequent CMP99
source estimate.  Nor is `indices.card` identified here with the integer `m`
in the printed CMP116 Lemma-1 split `m > 2^4`: that source-to-series
dictionary must be proved before the finite factor can be charged to the
printed `exp (m * kappa1)` budget.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v w

/-- The degree retained by one head carrier and a selected family of tail
carriers is the sum of all their cardinalities, including overlaps. -/
theorem cmp116WeakeningMultiplicityDegree_carrier_add_family
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (head : Finset Delta) (selected : Finset Index)
    (active : Index → Finset Delta) :
    cmp116WeakeningMultiplicityDegree
        (cmp116WeakeningCarrierMultiplicity head +
          cmp116WeakeningFamilyMultiplicity selected active) =
      head.card + ∑ i ∈ selected, (active i).card := by
  rw [cmp116WeakeningMultiplicityDegree_add,
    cmp116WeakeningMultiplicityDegree_carrier,
    cmp116WeakeningMultiplicityDegree_family]

/-- Selecting fewer tail factors can only decrease the total multiplicity
degree. -/
theorem cmp116WeakeningMultiplicityDegree_carrier_add_family_le
    {Delta : Type u} {Index : Type v}
    [DecidableEq Delta] [DecidableEq Index]
    (head : Finset Delta) (indices selected : Finset Index)
    (active : Index → Finset Delta) (hselected : selected ⊆ indices) :
    cmp116WeakeningMultiplicityDegree
        (cmp116WeakeningCarrierMultiplicity head +
          cmp116WeakeningFamilyMultiplicity selected active) ≤
      head.card + ∑ i ∈ indices, (active i).card := by
  rw [cmp116WeakeningMultiplicityDegree_carrier_add_family]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum_of_subset hselected) head.card

/-- One term of the omitted-subset expansion is bounded by the full-family
total-degree radial majorant. -/
theorem norm_cmp116ComplexWeakeningMultiplicityOmittedTerm_le
    {Delta : Type u} {Index : Type v} {E : Type w}
    [DecidableEq Delta] [DecidableEq Index]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (head : Finset Delta) (indices omitted : Finset Index)
    (active : Index → Finset Delta) (sigma : Delta → ℂ)
    (R : ℝ) (term : E) (hR : 1 ≤ R)
    (hcap : ∀ d, ‖sigma d‖ ≤ R) :
    ‖(((-1 : ℂ) ^ omitted.card) *
          cmp116ComplexWeakeningMultiplicityMonomial
            (cmp116WeakeningCarrierMultiplicity head +
              cmp116WeakeningFamilyMultiplicity
                (indices \ omitted) active) sigma) • term‖ ≤
      R ^ (head.card + ∑ i ∈ indices, (active i).card) * ‖term‖ := by
  have hselected : indices \ omitted ⊆ indices := Finset.sdiff_subset
  have hdegree :=
    cmp116WeakeningMultiplicityDegree_carrier_add_family_le
      head indices (indices \ omitted) active hselected
  have hterm :=
    norm_cmp116ComplexWeakeningMultiplicityTerm_le_radialMajorant
      (cmp116WeakeningCarrierMultiplicity head +
        cmp116WeakeningFamilyMultiplicity (indices \ omitted) active)
      term sigma R (fun d _ => hcap d)
  have hradial :
      R ^ cmp116WeakeningMultiplicityDegree
          (cmp116WeakeningCarrierMultiplicity head +
            cmp116WeakeningFamilyMultiplicity
              (indices \ omitted) active) * ‖term‖ ≤
        R ^ (head.card + ∑ i ∈ indices, (active i).card) * ‖term‖ :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hR hdegree) (norm_nonneg term)
  simpa [norm_smul, norm_mul, norm_pow] using hterm.trans hradial

/-- The complete finite omitted-subset expansion costs at most one common
radial majorant per subset.  The resulting factor is exactly bounded by
`2 ^ indices.card`; no cancellation between signs is used. -/
theorem sum_norm_cmp116ComplexWeakeningMultiplicityOmittedTerm_le
    {Delta : Type u} {Index : Type v} {E : Type w}
    [DecidableEq Delta] [DecidableEq Index]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (head : Finset Delta) (indices : Finset Index)
    (active : Index → Finset Delta) (sigma : Delta → ℂ)
    (R : ℝ) (term : E) (hR : 1 ≤ R)
    (hcap : ∀ d, ‖sigma d‖ ≤ R) :
    ∑ omitted ∈ indices.powerset,
        ‖(((-1 : ℂ) ^ omitted.card) *
            cmp116ComplexWeakeningMultiplicityMonomial
              (cmp116WeakeningCarrierMultiplicity head +
                cmp116WeakeningFamilyMultiplicity
                  (indices \ omitted) active) sigma) • term‖ ≤
      ((2 ^ indices.card : ℕ) : ℝ) *
        (R ^ (head.card + ∑ i ∈ indices, (active i).card) * ‖term‖) := by
  calc
    ∑ omitted ∈ indices.powerset,
        ‖(((-1 : ℂ) ^ omitted.card) *
            cmp116ComplexWeakeningMultiplicityMonomial
              (cmp116WeakeningCarrierMultiplicity head +
                cmp116WeakeningFamilyMultiplicity
                  (indices \ omitted) active) sigma) • term‖ ≤
        ∑ _omitted ∈ indices.powerset,
          R ^ (head.card + ∑ i ∈ indices, (active i).card) * ‖term‖ := by
      exact Finset.sum_le_sum fun omitted _homitted =>
        norm_cmp116ComplexWeakeningMultiplicityOmittedTerm_le
          head indices omitted active sigma R term
          hR hcap
    _ = ((2 ^ indices.card : ℕ) : ℝ) *
        (R ^ (head.card + ∑ i ∈ indices, (active i).card) * ‖term‖) := by
      simp [Finset.card_powerset]

end

end YangMills.RG
