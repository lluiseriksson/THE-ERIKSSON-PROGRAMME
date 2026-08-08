/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249ComplexNoncentralAliasQuotientVariation
import YangMills.RG.BalabanCMP89Eq249ComplexNoncentralAliasSumBound

/-!
# Uniform vertical variation of the CMP89 noncentral alias sum

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

The sealed quotient-variation estimate has two radial terms. The numerator
variation already pays `|q|_2^(-2)`. The denominator-variation term pays
`|q|_2^(-3)` after the literal fine-symbol budget is inserted; since every
noncentral alias has `|q|_2 >= pi > 1`, it is safely relaxed to the same
`|q|_2^(-2)` factor. One existing CMP89 (2.51) redistribution at `alpha=-1`
then controls both terms, and the finite alias fibre is summed without a
cardinality estimate.

No optimized trigonometric gap or factor-two fine-symbol variation is used.
No stabilized-denominator lower bound, joint `B0`, contour shift or physical
Green estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Constant before the final CMP89 (2.51) source-weight redistribution. -/
def cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant
    (rho : ℝ) : ℝ :=
  cmp89Eq248ComplexAliasPairVerticalConstant rho *
      (2 * (3 * Real.pi) ^ 2) +
    cmp89Eq248ComplexAliasPairStripConstant rho *
      (32 * (rho * Real.exp rho) * (3 * Real.pi) ^ 4)

/-- Pointwise constant after the literal `alpha=-1` redistribution. -/
def cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant
    (rho : ℝ) : ℝ :=
  cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant rho *
    3 ^ (1 - (-1 : ℝ))

/-- Uniform constant for the complete finite noncentral variation sum. -/
def cmp89Eq249ComplexNoncentralAliasSumVariationBound (rho : ℝ) : ℝ :=
  cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
    (∑' n : ℤ,
      cmp89Eq251OneDimensionalAliasWeight
        (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4

/-- One noncentral quotient variation has the same summable source exponent
as the already sealed absolute quotient. -/
theorem norm_cmp89Eq248ComplexAliasDenominatorSummand_sub_realSlice_le_sourceWeight
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j)) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass z m -
        cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass
          (cmp89Eq245ComplexMomentumRealSlice z) m‖ ≤
      cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
  let q : Fin 4 → ℝ :=
    fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let radius : ℝ := cmp89Eq251EuclideanNorm q
  let square : ℝ := cmp89Eq251MomentumSquare q
  let gap : ℝ := ((1 / (3 * Real.pi)) ^ 2 * square) / 2
  let eps : ℝ := rho * Real.exp rho
  let weight : ℝ := cmp89Eq251MultidimensionalAliasWeight 1 m
  let A : ℝ := cmp89Eq248ComplexAliasPairVerticalConstant rho
  let B : ℝ := cmp89Eq248ComplexAliasPairStripConstant rho
  let C : ℝ := (3 * Real.pi) ^ 2
  have hradial :=
    norm_cmp89Eq248ComplexAliasDenominatorSummand_sub_realSlice_le_radial
      (mass := mass) hrho hradius hm hm0 hp hreal himag hamplitude
  have hradiusPi : Real.pi ≤ radius := by
    exact pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp
  have hradiusOne : 1 ≤ radius := by
    linarith [Real.pi_gt_three]
  have hradiusPos : 0 < radius := zero_lt_one.trans_le hradiusOne
  have hsquarePos : 0 < square := by
    exact cmp89Eq251MomentumSquare_shift_pos hm0 hp
  have hsquareEq : radius ^ 2 = square := by
    exact sq_cmp89Eq251EuclideanNorm q
  have heps : 0 ≤ eps := by
    dsimp [eps]
    positivity
  have hepsRadius : eps ≤ radius := by
    dsimp [eps]
    nlinarith [Real.pi_gt_three]
  have hbudget :
      cmp89Eq249NoncentralComplexGapBudget rho q ≤ 8 * eps * radius := by
    rw [cmp89Eq249NoncentralComplexGapBudget]
    change eps * (4 * radius + 4 * eps) ≤ 8 * eps * radius
    calc
      eps * (4 * radius + 4 * eps) ≤
          eps * (4 * radius + 4 * radius) := by
        apply mul_le_mul_of_nonneg_left _ heps
        linarith
      _ = 8 * eps * radius := by ring
  have hgapInv : gap⁻¹ = 2 * C * square⁻¹ := by
    dsimp [gap, C]
    field_simp [Real.pi_ne_zero, ne_of_gt hsquarePos]
  have hcollapse : radius * square⁻¹ * square⁻¹ ≤ square⁻¹ := by
    have hradiusSquare : radius ≤ square := by
      rw [← hsquareEq]
      nlinarith
    have hinv0 : 0 ≤ square⁻¹ := inv_nonneg.mpr hsquarePos.le
    calc
      radius * square⁻¹ * square⁻¹ ≤
          square * square⁻¹ * square⁻¹ := by
        gcongr
      _ = square⁻¹ := by
        field_simp [ne_of_gt hsquarePos]
  have hA : 0 ≤ A := by
    dsimp [A, cmp89Eq248ComplexAliasPairVerticalConstant]
    rw [cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B, cmp89Eq248ComplexAliasPairStripConstant]
    rw [cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hweight : 0 ≤ weight := by
    exact cmp89Eq251MultidimensionalAliasWeight_nonneg 1 m
  have hsecond :
      (B * weight) * cmp89Eq249NoncentralComplexGapBudget rho q *
            (2 * C * square⁻¹) * (2 * C * square⁻¹) ≤
        (B * (32 * eps * C ^ 2)) * (square⁻¹ * weight) := by
    calc
      (B * weight) * cmp89Eq249NoncentralComplexGapBudget rho q *
            (2 * C * square⁻¹) * (2 * C * square⁻¹) ≤
          (B * weight) * (8 * eps * radius) *
            (2 * C * square⁻¹) * (2 * C * square⁻¹) := by
        gcongr
      _ = (B * (32 * eps * C ^ 2)) *
            ((radius * square⁻¹ * square⁻¹) * weight) := by ring
      _ ≤ (B * (32 * eps * C ^ 2)) * (square⁻¹ * weight) := by
        gcongr
  have hradialWeight :
      ‖cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass z m -
          cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass
            (cmp89Eq245ComplexMomentumRealSlice z) m‖ ≤
        cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant rho *
          (square⁻¹ * weight) := by
    calc
      ‖cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass z m -
          cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass
            (cmp89Eq245ComplexMomentumRealSlice z) m‖ ≤
          (A * weight) * gap⁻¹ +
            (B * weight) * cmp89Eq249NoncentralComplexGapBudget rho q *
              gap⁻¹ * gap⁻¹ := by
        simpa [q, gap, square, weight, A, B] using hradial
      _ = (A * weight) * (2 * C * square⁻¹) +
            (B * weight) * cmp89Eq249NoncentralComplexGapBudget rho q *
              (2 * C * square⁻¹) * (2 * C * square⁻¹) := by
        rw [hgapInv]
      _ ≤ (A * weight) * (2 * C * square⁻¹) +
            (B * (32 * eps * C ^ 2)) * (square⁻¹ * weight) :=
        add_le_add_right hsecond _
      _ = cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant rho *
          (square⁻¹ * weight) := by
        dsimp [A, B, C, eps, weight,
          cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant]
        ring
  have hpower : radius ^ ((-1 : ℝ) - 1) = square⁻¹ := by
    rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
      Real.rpow_neg hradiusPos.le, Real.rpow_two, hsquareEq]
  have hredistribute : square⁻¹ * weight ≤
      3 ^ (1 - (-1 : ℝ)) *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
    rw [← hpower]
    exact cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
      (d := 4) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num) hm0 hp
  have hconstant :
      0 ≤ cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant rho := by
    rw [cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant]
    positivity
  calc
    ‖cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass z m -
        cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass
          (cmp89Eq245ComplexMomentumRealSlice z) m‖ ≤
      cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant rho *
        (square⁻¹ * weight) := hradialWeight
    _ ≤ cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant rho *
        (3 ^ (1 - (-1 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m) :=
      mul_le_mul_of_nonneg_left hredistribute hconstant
    _ = cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
      rw [cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant]
      ring

/-- The complete finite noncentral alias sum varies uniformly in the block
count, with no reciprocal-fibre cardinality factor. -/
theorem norm_cmp89Eq249ComplexNoncentralAliasSum_sub_realSlice_le_bound
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z -
        cmp89Eq249ComplexNoncentralAliasSum 4 L j mass
          (cmp89Eq245ComplexMomentumRealSlice z)‖ ≤
      cmp89Eq249ComplexNoncentralAliasSumVariationBound rho := by
  let aliases := cmp89Eq245CenteredAliasVectors 4 (L ^ j)
  let zeroAlias := cmp89Eq249ZeroAlias 4
  let term : (Fin 4 → ℤ) → (Fin 4 → ℂ) → ℂ := fun m w =>
    cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass w m
  let weight : (Fin 4 → ℤ) → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) m
  have hconstant :
      0 ≤ cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho := by
    rw [cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant,
      cmp89Eq249ComplexNoncentralAliasQuotientVariationRadialConstant]
    unfold cmp89Eq248ComplexAliasPairVerticalConstant
      cmp89Eq248ComplexAliasPairStripConstant
      cmp89Eq245EntireAverageAliasStripConstant
    positivity
  have hpointwise : ∀ m ∈ aliases.erase zeroAlias,
      ‖term m z - term m (cmp89Eq245ComplexMomentumRealSlice z)‖ ≤
        cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
          weight m := by
    intro m hm
    have hmParts := Finset.mem_erase.mp hm
    have hm0 : m ≠ 0 := by
      simpa only [zeroAlias, cmp89Eq249ZeroAlias] using hmParts.1
    exact norm_cmp89Eq248ComplexAliasDenominatorSummand_sub_realSlice_le_sourceWeight
      hrho hradius hmParts.2 hm0 hp hreal himag hamplitude
  have hfinite :
      ‖∑ m ∈ aliases.erase zeroAlias,
          (term m z - term m (cmp89Eq245ComplexMomentumRealSlice z))‖ ≤
        cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
          (∑ m ∈ aliases, weight m) := by
    calc
      ‖∑ m ∈ aliases.erase zeroAlias,
          (term m z - term m (cmp89Eq245ComplexMomentumRealSlice z))‖ ≤
        ∑ m ∈ aliases.erase zeroAlias,
          ‖term m z - term m (cmp89Eq245ComplexMomentumRealSlice z)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ aliases.erase zeroAlias,
          cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
            weight m := Finset.sum_le_sum hpointwise
      _ = cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
          ∑ m ∈ aliases.erase zeroAlias, weight m := by
        rw [Finset.mul_sum]
      _ ≤ cmp89Eq249ComplexNoncentralAliasQuotientVariationConstant rho *
          ∑ m ∈ aliases, weight m := by
        apply mul_le_mul_of_nonneg_left _ hconstant
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset zeroAlias aliases)
          (fun m _ _ => cmp89Eq251MultidimensionalAliasWeight_nonneg _ m)
  have hseries : (∑ m ∈ aliases, weight m) ≤
      (∑' n : ℤ,
        cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4 := by
    simpa [aliases, weight] using
      (cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
        (d := 4) (L ^ j) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num))
  rw [cmp89Eq249ComplexNoncentralAliasSum,
    cmp89Eq249ComplexNoncentralAliasSum,
    cmp89Eq249ComplexNoncentralAliasSumVariationBound]
  change ‖(∑ m ∈ aliases.erase zeroAlias, term m z) -
      ∑ m ∈ aliases.erase zeroAlias,
        term m (cmp89Eq245ComplexMomentumRealSlice z)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  exact hfinite.trans (mul_le_mul_of_nonneg_left hseries hconstant)

end

end YangMills.RG
