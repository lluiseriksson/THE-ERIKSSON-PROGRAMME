/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249UniformNoncentralComplexRadius
import YangMills.RG.BalabanCMP89Eq251AliasWeightRedistribution
import YangMills.RG.BalabanCMP89Eq251EntireScaledDifferenceStripUpper

/-!
# PRE-VALIDATION: noncentral endpoint quotient below CMP89 (2.51)

Source is present, its `.olean` has not yet been materialized, and the results
have not yet been verified by the compiler.

One physical endpoint retains one scaled lattice difference, one entire
averaging amplitude and one inverse fine symbol.  The difference cancels one
of the two inverse momentum powers supplied by the complex fine-symbol gap.
Consequently the source-weight redistribution is the literal specialization
`alpha = 0`, not the `alpha = -1` specialization used for the opposite-
momentum denominator pair.

Every constant remains explicit.  This file proves only a pointwise
noncentral quotient bound.  It does not insert the endpoint phase or Holder
normalization, sum aliases, assemble the central branch, construct `B0`,
transport to localization owners, attain window 15 or discharge a terminal
field.
-/

namespace YangMills.RG

noncomputable section

/-- Constant before the `alpha = 0` alias-exponent redistribution. -/
def cmp89Eq251ComplexNoncentralEndpointRadialConstant (rho : ℝ) : ℝ :=
  4 * (3 * Real.pi) ^ 2 *
    cmp89Eq245EntireAverageAliasStripConstant rho ^ 4

/-- Explicit constant multiplying the summable product weight for one
noncentral endpoint quotient. -/
def cmp89Eq251ComplexNoncentralEndpointQuotientConstant (rho : ℝ) : ℝ :=
  cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
    3 ^ (1 - (0 : ℝ))

/-- On a noncentral reciprocal alias, one scaled difference costs at most
twice the Euclidean alias momentum.  The factor two keeps the real and
vertical contributions visible before they are combined. -/
theorem norm_cmp89Eq245EntireScaledDifference_alias_le_two_euclidean
    {N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 ≤ rho)
    {m : Fin 4 → ℤ} (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹
        (-(cmp89Eq248EntireAliasMomentum z m mu))‖ ≤
      2 * cmp89Eq251EuclideanNorm
        (fun nu => p nu + 2 * Real.pi * (m nu : ℝ)) := by
  let q : Fin 4 → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hxi : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNreal
  have hxi1 : (N : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hNreal]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hN))
  have haliasReal : ∀ nu, (aliasZ nu).re = q nu := by
    intro nu
    simp [aliasZ, q, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal nu]
  have haliasImag : ∀ nu, |(aliasZ nu).im| ≤ rho := by
    intro nu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag nu
  have hraw :=
    norm_cmp89Eq245EntireScaledDifference_le_abs_re_add_vertical
      hxi hxi1 hrho (by simpa using haliasImag mu)
  have hpi : Real.pi ≤ cmp89Eq251EuclideanNorm q :=
    pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp
  have heps : rho * Real.exp rho ≤ cmp89Eq251EuclideanNorm q := by
    have hsixth : (1 / 6 : ℝ) ≤ Real.pi := by
      linarith [Real.pi_gt_three]
    exact hamplitude.trans (hsixth.trans hpi)
  have hcoord : |q mu| ≤ cmp89Eq251EuclideanNorm q :=
    abs_le_cmp89Eq251EuclideanNorm q mu
  calc
    ‖cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹
        (-(cmp89Eq248EntireAliasMomentum z m mu))‖ ≤
      |(-(aliasZ mu)).re| + rho * Real.exp rho := by
        simpa [aliasZ] using hraw
    _ = |q mu| + rho * Real.exp rho := by
      rw [Complex.neg_re, haliasReal, abs_neg]
    _ ≤ cmp89Eq251EuclideanNorm q + cmp89Eq251EuclideanNorm q :=
      add_le_add hcoord heps
    _ = 2 * cmp89Eq251EuclideanNorm q := by ring

/-- Before redistribution, the endpoint quotient retains one inverse radial
power and one reciprocal-alias product weight. -/
theorem norm_cmp89Eq251ComplexNoncentralEndpointQuotient_le_radialWeight
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹
          (-(cmp89Eq248EntireAliasMomentum z m mu)) *
        cmp89Eq245EntireAverageAmplitude 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
        (cmp89Eq251EuclideanNorm
            (fun nu => p nu + 2 * Real.pi * (m nu : ℝ)) ^
              ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
  let q : Fin 4 → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m
  have haliasReal : ∀ nu, (aliasZ nu).re = q nu := by
    intro nu
    simp [aliasZ, q, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal nu]
  have haliasImag : ∀ nu, |(aliasZ nu).im| ≤ rho := by
    intro nu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag nu
  have hdiff :
      ‖cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹ (-(aliasZ mu))‖ ≤
        2 * cmp89Eq251EuclideanNorm q := by
    simpa [q, aliasZ] using
      (norm_cmp89Eq245EntireScaledDifference_alias_le_two_euclidean
        hN hrho hm0 hp hreal himag hamplitude mu)
  have havg :
      ‖cmp89Eq245EntireAverageAmplitude 4 N aliasZ‖ ≤
        cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
          cmp89Eq251MultidimensionalAliasWeight 1 m := by
    exact norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le
      hN hm hrho hp haliasReal haliasImag hamplitude
  have hden :
      ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2 ≤
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖ := by
    simpa only [q] using
      half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_of_uniformRadius
        hN hrho hradius hm hm0 hp haliasReal haliasImag
  have hqNorm : 0 < cmp89Eq251EuclideanNorm q :=
    Real.pi_pos.trans_le (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)
  have hqSquare : 0 < cmp89Eq251MomentumSquare q := by
    rw [← sq_cmp89Eq251EuclideanNorm]
    positivity
  have hgap :
      0 < ((1 / (3 * Real.pi)) ^ 2 *
        cmp89Eq251MomentumSquare q) / 2 := by positivity
  have hdenInv :
      ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖⁻¹ ≤
        (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hgap hden
  have hgapInv :
      (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ =
        2 * (3 * Real.pi) ^ 2 *
          (cmp89Eq251MomentumSquare q)⁻¹ := by
    field_simp [Real.pi_ne_zero, ne_of_gt hqSquare]
  have hradialCancel :
      cmp89Eq251EuclideanNorm q *
          (cmp89Eq251MomentumSquare q)⁻¹ =
        cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) := by
    rw [← sq_cmp89Eq251EuclideanNorm]
    rw [show ((0 : ℝ) - 1) = -1 by norm_num,
      Real.rpow_neg hqNorm.le, Real.rpow_one]
    field_simp [ne_of_gt hqNorm]
  have hweightNonneg :
      0 ≤ cmp89Eq251MultidimensionalAliasWeight 1 m :=
    cmp89Eq251MultidimensionalAliasWeight_nonneg 1 m
  have hconstantNonneg :
      0 ≤ cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 :=
    pow_nonneg (by
      rw [cmp89Eq245EntireAverageAliasStripConstant]
      positivity) 4
  rw [show cmp89Eq248EntireAliasMomentum z m = aliasZ by rfl,
    norm_div, norm_mul, div_eq_mul_inv]
  calc
    ‖cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹ (-(aliasZ mu))‖ *
          ‖cmp89Eq245EntireAverageAmplitude 4 N aliasZ‖ *
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖⁻¹ ≤
      (2 * cmp89Eq251EuclideanNorm q) *
          (cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
            cmp89Eq251MultidimensionalAliasWeight 1 m) *
        (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
      gcongr
    _ = cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
        (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
      rw [hgapInv, ← hradialCancel,
        cmp89Eq251ComplexNoncentralEndpointRadialConstant]
      ring

/-- Final source-weight bound for one noncentral endpoint quotient.  Its
exponent is `1 + 1/4`, the literal CMP89 redistribution at `alpha = 0`. -/
theorem norm_cmp89Eq251ComplexNoncentralEndpointQuotient_le_sourceWeight
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹
          (-(cmp89Eq248EntireAliasMomentum z m mu)) *
        cmp89Eq245EntireAverageAmplitude 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 0) m := by
  let q : Fin 4 → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  have hradial :=
    norm_cmp89Eq251ComplexNoncentralEndpointQuotient_le_radialWeight
      hN hrho hradius hm hm0 hp hreal himag hamplitude mu
  have hredistribute :
      cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - (0 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 0) m := by
    exact cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
      (d := 4) (alpha := (0 : ℝ)) (by norm_num) (by norm_num) hm0 hp
  have hradialConstant :
      0 ≤ cmp89Eq251ComplexNoncentralEndpointRadialConstant rho := by
    rw [cmp89Eq251ComplexNoncentralEndpointRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  calc
    ‖cmp89Eq245EntireScaledDifference (N : ℝ)⁻¹
          (-(cmp89Eq248EntireAliasMomentum z m mu)) *
        cmp89Eq245EntireAverageAmplitude 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
        (cmp89Eq251EuclideanNorm q ^ ((0 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
      simpa only [q] using hradial
    _ ≤ cmp89Eq251ComplexNoncentralEndpointRadialConstant rho *
        (3 ^ (1 - (0 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 0) m) :=
      mul_le_mul_of_nonneg_left hredistribute hradialConstant
    _ = cmp89Eq251ComplexNoncentralEndpointQuotientConstant rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 0) m := by
      rw [cmp89Eq251ComplexNoncentralEndpointQuotientConstant]
      ring

end

end YangMills.RG
