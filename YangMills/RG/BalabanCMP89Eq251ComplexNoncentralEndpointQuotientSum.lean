/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexNoncentralEndpointQuotientBound

/-!
# PRE-VALIDATION: noncentral endpoint quotient sum below CMP89 (2.51)

Source is present, its `.olean` has not yet been materialized, and the results
have not yet been verified by the compiler.

The pointwise endpoint quotient bound already carries the strictly summable
CMP89 product weight with the literal specialization `alpha = 0`.  This file
sums it over the printed finite reciprocal-alias fibre, removes the central
alias without a cardinality estimate, and applies the sealed product/tsum
bound at that same specialization.

This file does not insert the endpoint phase or Holder normalization, assemble
the central endpoint branch, construct `B0`, transport to localization owners,
attain window 15 or discharge a terminal field.
-/

namespace YangMills.RG

noncomputable section

/-- The finite sum of noncentral fine-symbol quotients occurring inside one
stabilized endpoint numerator. -/
def cmp89Eq251ComplexNoncentralEndpointQuotientSum
    (L j : ℕ) (mass : ℝ) (z : Fin 4 → ℂ) (mu : Fin 4) : ℂ :=
  ∑ m ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
      (cmp89Eq249ZeroAlias 4),
    cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹)
        (-(cmp89Eq248EntireAliasMomentum z m mu)) *
      cmp89Eq245EntireAverageAmplitude 4 (L ^ j)
        (cmp89Eq248EntireAliasMomentum z m) /
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m)

/-- Explicit scale-uniform majorant for the complete noncentral endpoint
quotient sum. -/
def cmp89Eq251ComplexNoncentralEndpointQuotientSumBound (rho : ℝ) : ℝ :=
  cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
    (∑' n : ℤ,
      cmp89Eq251OneDimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent 4 0) n) ^ 4

/-- The complete finite noncentral endpoint quotient sum is bounded uniformly
in the alias count.  No fibre-cardinality factor is introduced. -/
theorem norm_cmp89Eq251ComplexNoncentralEndpointQuotientSum_le_bound
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq251ComplexNoncentralEndpointQuotientSum L j mass z mu‖ ≤
      cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho := by
  let N : ℕ := L ^ j
  let aliases := cmp89Eq245CenteredAliasVectors 4 N
  let zeroAlias := cmp89Eq249ZeroAlias 4
  let term : (Fin 4 → ℤ) → ℂ := fun m =>
    cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹
        (-(cmp89Eq248EntireAliasMomentum z m mu)) *
      cmp89Eq245EntireAverageAmplitude 4 N
        (cmp89Eq248EntireAliasMomentum z m) /
      cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
        (cmp89Eq248EntireAliasMomentum z m)
  let weight : (Fin 4 → ℤ) → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 0) m
  have hN : 0 < N := by
    exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hconstantNonneg :
      0 ≤ cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho := by
    rw [cmp89Eq251ComplexNoncentralEndpointQuotientConstant,
      cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpointwise :
      ∀ m ∈ aliases.erase zeroAlias,
        ‖term m‖ ≤
          cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho * weight m := by
    intro m hm
    have hmParts := Finset.mem_erase.mp hm
    have hm0 : m ≠ 0 := by
      simpa only [zeroAlias, cmp89Eq249ZeroAlias] using hmParts.1
    have hbound :=
      norm_cmp89Eq251ComplexNoncentralEndpointQuotient_le_sourceWeight
        (mass := mass) hN hrho hradius hmParts.2 hm0 hp hreal himag
        hamplitude mu
    simpa only [term, weight, N, Nat.cast_pow] using hbound
  have heraseWeight :
      (∑ m ∈ aliases.erase zeroAlias, weight m) ≤
        ∑ m ∈ aliases, weight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset zeroAlias aliases)
      (fun m _ _ =>
        cmp89Eq251MultidimensionalAliasWeight_nonneg
          (cmp89Eq251AliasSeriesExponent 4 0) m)
  have hfinite :
      ‖∑ m ∈ aliases.erase zeroAlias, term m‖ ≤
        cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
          (∑ m ∈ aliases, weight m) := by
    calc
      ‖∑ m ∈ aliases.erase zeroAlias, term m‖ ≤
          ∑ m ∈ aliases.erase zeroAlias, ‖term m‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ aliases.erase zeroAlias,
          cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho * weight m :=
        Finset.sum_le_sum hpointwise
      _ = cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
          (∑ m ∈ aliases.erase zeroAlias, weight m) := by
        rw [Finset.mul_sum]
      _ ≤ cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
          (∑ m ∈ aliases, weight m) :=
        mul_le_mul_of_nonneg_left heraseWeight hconstantNonneg
  have hseries :
      (∑ m ∈ aliases, weight m) ≤
        (∑' n : ℤ,
          cmp89Eq251OneDimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 0) n) ^ 4 := by
    simpa only [aliases, weight, N] using
      (cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
        (d := 4) N (alpha := (0 : ℝ)) (by norm_num) (by norm_num))
  rw [cmp89Eq251ComplexNoncentralEndpointQuotientSum,
    cmp89Eq251ComplexNoncentralEndpointQuotientSumBound]
  change ‖∑ m ∈ aliases.erase zeroAlias, term m‖ ≤ _
  exact hfinite.trans
    (mul_le_mul_of_nonneg_left hseries hconstantNonneg)

end

end YangMills.RG
