/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAverageAliasWeightedVariation
import YangMills.RG.BalabanCMP89Eq249ComplexNoncentralAliasQuotientBound

/-!
# Vertical variation of one complex noncentral CMP89 alias quotient

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

This module combines the sealed alias-weighted variation of the averaging
pair with the sealed complex fine-symbol gap. The quotient rule is kept as an
explicit two-term norm estimate: numerator variation pays one inverse gap,
whereas denominator variation pays two. The real slice and complex point use
the same moment-dependent radial gap.

No reciprocal-alias cardinality is introduced and no symmetry of the
half-open centered alias fibre is assumed. The radial powers have not yet
been redistributed into the final CMP89 (2.51) source exponent, and the
finite quotient variation has not yet been summed.

No stabilized-denominator lower bound, joint `B0`, contour shift or physical
Green estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Quotient variation from lower bounds for both denominators. The two
inverse-gap costs remain separate and no complex differentiability is used. -/
theorem norm_div_sub_div_le_of_lower_bounds
    {u u0 den den0 : ℂ} {uVar u0Bound denVar gap gap0 : ℝ}
    (hgap : 0 < gap) (hgap0 : 0 < gap0)
    (huVar : ‖u - u0‖ ≤ uVar) (hu0 : ‖u0‖ ≤ u0Bound)
    (hdenVar : ‖den - den0‖ ≤ denVar)
    (hden : gap ≤ ‖den‖) (hden0 : gap0 ≤ ‖den0‖) :
    ‖u / den - u0 / den0‖ ≤
      uVar * gap⁻¹ + u0Bound * denVar * gap⁻¹ * gap0⁻¹ := by
  have hdenPos : 0 < ‖den‖ := hgap.trans_le hden
  have hden0Pos : 0 < ‖den0‖ := hgap0.trans_le hden0
  have hdenNe : den ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenPos
    exact lt_irrefl 0 hdenPos
  have hden0Ne : den0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden0Pos
    exact lt_irrefl 0 hden0Pos
  have hdenInv : ‖den‖⁻¹ ≤ gap⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hgap hden
  have hden0Inv : ‖den0‖⁻¹ ≤ gap0⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hgap0 hden0
  have hrewrite :
      u / den - u0 / den0 =
        (u - u0) * den⁻¹ + u0 * (den0 - den) * den⁻¹ * den0⁻¹ := by
    field_simp [hdenNe, hden0Ne]
    ring
  rw [hrewrite]
  calc
    ‖(u - u0) * den⁻¹ + u0 * (den0 - den) * den⁻¹ * den0⁻¹‖ ≤
        ‖(u - u0) * den⁻¹‖ +
          ‖u0 * (den0 - den) * den⁻¹ * den0⁻¹‖ := norm_add_le _ _
    _ = ‖u - u0‖ * ‖den‖⁻¹ +
        ‖u0‖ * ‖den0 - den‖ * ‖den‖⁻¹ * ‖den0‖⁻¹ := by
      simp only [norm_mul, norm_inv]
    _ ≤ uVar * gap⁻¹ +
        u0Bound * denVar * gap⁻¹ * gap0⁻¹ := by
      have huVar0 : 0 ≤ uVar := (norm_nonneg _).trans huVar
      have hu0Bound0 : 0 ≤ u0Bound := (norm_nonneg _).trans hu0
      have hdenVar0 : 0 ≤ denVar := (norm_nonneg _).trans hdenVar
      exact add_le_add
        (mul_le_mul huVar hdenInv (inv_nonneg.mpr (norm_nonneg _)) huVar0)
        (by
          have hrev : ‖den0 - den‖ ≤ denVar := by
            simpa [norm_sub_rev] using hdenVar
          gcongr)

/-- Exact commutation of alias translation with projection to the real slice.
The reciprocal shift is real, so no geometric premise is needed. -/
theorem cmp89Eq248EntireAliasMomentum_realSlice_eq
    {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℤ) :
    cmp89Eq248EntireAliasMomentum
        (cmp89Eq245ComplexMomentumRealSlice z) m =
      cmp89Eq245ComplexMomentumRealSlice
        (cmp89Eq248EntireAliasMomentum z m) := by
  funext mu
  simp [cmp89Eq248EntireAliasMomentum,
    cmp89Eq245ComplexMomentumRealSlice]

/-- Coefficient of the retained source weight in the averaging-pair vertical
variation, specialized to four dimensions. -/
def cmp89Eq248ComplexAliasPairVerticalConstant (rho : ℝ) : ℝ :=
  2 * (4 * (rho * Real.exp rho) * (Real.exp rho) ^ 4) *
    cmp89Eq245EntireAverageAliasStripConstant rho ^ 4

/-- Coefficient of the retained source weight in the absolute averaging-pair
strip bound, specialized to four dimensions. -/
def cmp89Eq248ComplexAliasPairStripConstant (rho : ℝ) : ℝ :=
  cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 * Real.exp rho ^ 4

/-- Pointwise vertical variation of one literal noncentral quotient. The
momentum-dependent gap and the complete fine-symbol variation budget remain
visible for the subsequent source-weight redistribution. -/
theorem norm_cmp89Eq248ComplexAliasDenominatorSummand_sub_realSlice_le_radial
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j)) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    let q : Fin 4 → ℝ :=
      fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
    let gap : ℝ :=
      ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2
    ‖cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass z m -
        cmp89Eq248ComplexAliasDenominatorSummand 4 L j mass
          (cmp89Eq245ComplexMomentumRealSlice z) m‖ ≤
      (cmp89Eq248ComplexAliasPairVerticalConstant rho *
          cmp89Eq251MultidimensionalAliasWeight 1 m) * gap⁻¹ +
        (cmp89Eq248ComplexAliasPairStripConstant rho *
          cmp89Eq251MultidimensionalAliasWeight 1 m) *
          cmp89Eq249NoncentralComplexGapBudget rho q * gap⁻¹ * gap⁻¹ := by
  let N : ℕ := L ^ j
  let q : Fin 4 → ℝ :=
    fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let gap : ℝ :=
    ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m
  let aliasZ0 : Fin 4 → ℂ := cmp89Eq245ComplexMomentumRealSlice aliasZ
  let pair := cmp89Eq245EntireAveragePair 4 N aliasZ
  let pair0 := cmp89Eq245EntireAveragePair 4 N aliasZ0
  let den := cmp89Eq245EntireScaledLaplacianSymbol
    4 (N : ℝ)⁻¹ mass aliasZ
  let den0 := cmp89Eq245EntireScaledLaplacianSymbol
    4 (N : ℝ)⁻¹ mass aliasZ0
  have hN : 0 < N := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have haliasReal : ∀ mu, (aliasZ mu).re = q mu := by
    intro mu
    simp [aliasZ, q, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal mu]
  have haliasImag : ∀ mu, |(aliasZ mu).im| ≤ rho := by
    intro mu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag mu
  have hpairVar : ‖pair - pair0‖ ≤
      cmp89Eq248ComplexAliasPairVerticalConstant rho *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
    simpa [pair, pair0, aliasZ0,
      cmp89Eq248ComplexAliasPairVerticalConstant] using
      (norm_cmp89Eq245EntireAveragePair_alias_sub_realSlice_le
        (d := 4) (N := N) hN hm hrho hp hreal himag hamplitude)
  have hpair0 : ‖pair0‖ ≤
      cmp89Eq248ComplexAliasPairStripConstant rho *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
    have hzeroImag : ∀ mu, |(aliasZ0 mu).im| ≤ rho := by
      intro mu
      simp [aliasZ0, cmp89Eq245ComplexMomentumRealSlice, hrho]
    have hbound :=
      norm_cmp89Eq245EntireAveragePair_scaled_alias_le
        (N := N) hN hm hrho hp (z := aliasZ0)
        (fun mu => by simp [aliasZ0, cmp89Eq245ComplexMomentumRealSlice,
          haliasReal mu, q])
        hzeroImag hamplitude
    simpa [pair0, cmp89Eq248ComplexAliasPairStripConstant] using hbound
  have hgapPos : 0 < gap := by
    have hq : 0 < cmp89Eq251MomentumSquare q :=
      cmp89Eq251MomentumSquare_shift_pos hm0 hp
    dsimp [gap]
    positivity
  have hden : gap ≤ ‖den‖ := by
    simpa [den, gap, q] using
      (half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_of_uniformRadius
        (mass := mass) hN hrho hradius hm hm0 hp haliasReal haliasImag)
  have hden0 : gap ≤ ‖den0‖ := by
    have hzeroImag : ∀ mu, |(aliasZ0 mu).im| ≤ rho := by
      intro mu
      simp [aliasZ0, cmp89Eq245ComplexMomentumRealSlice, hrho]
    simpa [den0, gap, q] using
      (half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_of_uniformRadius
        (mass := mass) hN hrho hradius hm hm0 hp
        (z := aliasZ0)
        (fun mu => by
          simp [aliasZ0, cmp89Eq245ComplexMomentumRealSlice,
            haliasReal mu, q])
        hzeroImag)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hxi : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNreal
  have hxi1 : (N : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hNreal]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN))
  have hdenVar : ‖den - den0‖ ≤
      cmp89Eq249NoncentralComplexGapBudget rho q := by
    have hraw :=
      norm_cmp89Eq245EntireScaledLaplacianSymbol_sub_realSlice_le
        (mass := mass) hxi hxi1 hrho haliasImag
    have hbudget :=
      cmp89Eq245EntireScaledLaplacianVerticalBudget_le_noncentralGapBudget
        hrho haliasReal
    have hraw' : ‖den - den0‖ ≤
        cmp89Eq245EntireScaledLaplacianVerticalBudget 4 rho aliasZ := by
      simpa [den, den0, aliasZ0] using hraw
    exact hraw'.trans hbudget
  have hquot := norm_div_sub_div_le_of_lower_bounds
    hgapPos hgapPos hpairVar hpair0 hdenVar hden hden0
  have haliasSlice :
      cmp89Eq248EntireAliasMomentum
          (cmp89Eq245ComplexMomentumRealSlice z) m = aliasZ0 := by
    simpa [aliasZ0, aliasZ] using
      (cmp89Eq248EntireAliasMomentum_realSlice_eq z m)
  simpa [cmp89Eq248ComplexAliasDenominatorSummand, N, aliasZ, aliasZ0,
    pair, pair0, den, den0, haliasSlice, q, gap] using hquot

end

end YangMills.RG
