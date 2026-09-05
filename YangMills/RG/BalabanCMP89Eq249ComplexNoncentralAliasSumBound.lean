/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249ComplexNoncentralAliasQuotientBound

/-!
# Uniform finite complex noncentral alias sum in CMP89 (2.47)--(2.49)

The pointwise complex quotient bound already has the strictly summable CMP89
(2.51) product weight.  This module sums it over the literal finite alias
fibre, removes the central alias without a cardinality estimate, and applies
the sealed product/tsum bound at `alpha = -1`.

The output is uniform in the block count `L^j`.  It still depends on the two
separate strip conditions: amplitude control and the noncentral complex gap.
No stabilized-denominator lower bound, `B0`, contour shift or physical Green
estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit scale-uniform majorant for the complete noncentral complex alias
sum. -/
def cmp89Eq249ComplexNoncentralAliasSumBound (rho : ℝ) : ℝ :=
  cmp89Eq249ComplexNoncentralAliasQuotientConstant rho *
    (∑' n : ℤ,
      cmp89Eq251OneDimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4

/-- The complete finite noncentral complex alias sum is bounded uniformly in
the alias count, with no fibre-cardinality factor. -/
theorem norm_cmp89Eq249ComplexNoncentralAliasSum_le_bound
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z‖ ≤
      cmp89Eq249ComplexNoncentralAliasSumBound rho := by
  let N : ℕ := L ^ j
  let aliases := cmp89Eq245CenteredAliasVectors 4 N
  let zeroAlias := cmp89Eq249ZeroAlias 4
  let term : (Fin 4 → ℤ) → ℂ := fun m =>
    cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass z m
  let weight : (Fin 4 → ℤ) → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) m
  have hN : 0 < N := by
    exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hconstantNonneg :
      0 ≤ cmp89Eq249ComplexNoncentralAliasQuotientConstant rho := by
    rw [cmp89Eq249ComplexNoncentralAliasQuotientConstant,
      cmp89Eq249ComplexNoncentralAliasRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpointwise :
      ∀ m ∈ aliases.erase zeroAlias,
        ‖term m‖ ≤
          cmp89Eq249ComplexNoncentralAliasQuotientConstant rho * weight m := by
    intro m hm
    have hmParts := Finset.mem_erase.mp hm
    have hm0 : m ≠ 0 := by
      simpa only [zeroAlias, cmp89Eq249ZeroAlias] using hmParts.1
    have hbound :=
      norm_cmp89Eq248ComplexAliasDenominatorSummand_le_sourceWeight
        (mass := mass) hN hrho hradius hmParts.2 hm0 hp hreal himag hamplitude
    simpa only [term, weight, N, Nat.cast_pow,
      cmp89Eq248ComplexAliasDenominatorSummand] using hbound
  have heraseWeight :
      (∑ m ∈ aliases.erase zeroAlias, weight m) ≤
        ∑ m ∈ aliases, weight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset zeroAlias aliases)
      (fun m _ _ =>
        cmp89Eq251MultidimensionalAliasWeight_nonneg
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m)
  have hfinite :
      ‖∑ m ∈ aliases.erase zeroAlias, term m‖ ≤
        cmp89Eq249ComplexNoncentralAliasQuotientConstant rho *
          (∑ m ∈ aliases, weight m) := by
    calc
      ‖∑ m ∈ aliases.erase zeroAlias, term m‖ ≤
          ∑ m ∈ aliases.erase zeroAlias, ‖term m‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ aliases.erase zeroAlias,
          cmp89Eq249ComplexNoncentralAliasQuotientConstant rho * weight m :=
        Finset.sum_le_sum hpointwise
      _ = cmp89Eq249ComplexNoncentralAliasQuotientConstant rho *
          (∑ m ∈ aliases.erase zeroAlias, weight m) := by
        rw [Finset.mul_sum]
      _ ≤ cmp89Eq249ComplexNoncentralAliasQuotientConstant rho *
          (∑ m ∈ aliases, weight m) :=
        mul_le_mul_of_nonneg_left heraseWeight hconstantNonneg
  have hseries :
      (∑ m ∈ aliases, weight m) ≤
        (∑' n : ℤ,
          cmp89Eq251OneDimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4 := by
    simpa only [aliases, weight, N] using
      (cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
        (d := 4) N (alpha := (-1 : ℝ)) (by norm_num) (by norm_num))
  rw [cmp89Eq249ComplexNoncentralAliasSum,
    cmp89Eq249ComplexNoncentralAliasSumBound]
  change ‖∑ m ∈ aliases.erase zeroAlias, term m‖ ≤ _
  exact hfinite.trans
    (mul_le_mul_of_nonneg_left hseries hconstantNonneg)

end

end YangMills.RG
