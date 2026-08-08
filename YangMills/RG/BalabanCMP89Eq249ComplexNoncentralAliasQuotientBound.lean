/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAverageAliasStripBound
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedAliasDenominator
import YangMills.RG.BalabanCMP89Eq249UniformNoncentralComplexRadius
import YangMills.RG.BalabanCMP89Eq251AliasWeightRedistribution

/-!
# Alias-weighted complex noncentral quotient in CMP89 (2.47)--(2.49)

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

The noncentral complex denominator summand is an opposite-momentum averaging
pair divided by the entire fine symbol.  One averaging amplitude retains the
sealed reciprocal-alias weight; the opposite amplitude uses only the uniform
strip-growth bound.  This avoids assuming that the half-open centered alias
set is invariant under negation.

The sealed uniform-radius condition supplies the moment-dependent complex
gap.  Its inverse contributes `|q|_2^(-2)`, which is redistributed into the
already summable source weight by the existing CMP89 (2.51) theorem at the
literal specialization `alpha = -1`.  The amplitude condition
`rho * exp rho <= 1/6` and the complex-gap radius condition remain distinct.

This module proves a pointwise quotient bound only.  It does not yet sum the
noncentral aliases, lower-bound the stabilized denominator, construct `B0`,
shift a contour or identify a Fourier rate with physical Green decay.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Constant before the final alias-exponent redistribution. -/
def cmp89Eq249ComplexNoncentralAliasRadialConstant (rho : ℝ) : ℝ :=
  2 * (3 * Real.pi) ^ 2 *
    cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
    Real.exp rho ^ 4

/-- Explicit pointwise constant multiplying the summable product weight. -/
def cmp89Eq249ComplexNoncentralAliasQuotientConstant (rho : ℝ) : ℝ :=
  cmp89Eq249ComplexNoncentralAliasRadialConstant rho *
    3 ^ (1 - (-1 : ℝ))

/-- In four dimensions, one side of the opposite-momentum pair retains the
reciprocal-alias weight while the other pays only uniform strip growth. -/
theorem norm_cmp89Eq245EntireAveragePair_scaled_alias_le
    {N : ℕ} (hN : 0 < N) {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N)
    {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re =
      p mu + 2 * Real.pi * (m mu : ℝ))
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAveragePair 4 N z‖ ≤
      cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
        Real.exp rho ^ 4 *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  have hweighted :=
    norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le
      hN hm hrho hp hreal himag hamplitude
  have hopposite :
      ‖cmp89Eq245EntireAverageAmplitude 4 N (-z)‖ ≤
        Real.exp rho ^ 4 := by
    apply norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow hN hrho
    intro mu
    simpa using himag mu
  have hstripNonneg :
      0 ≤ cmp89Eq245EntireAverageAliasStripConstant rho := by
    rw [cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  rw [cmp89Eq245EntireAveragePair, norm_mul]
  calc
    ‖cmp89Eq245EntireAverageAmplitude 4 N z‖ *
        ‖cmp89Eq245EntireAverageAmplitude 4 N (-z)‖ ≤
      (cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
          cmp89Eq251MultidimensionalAliasWeight 1 m) *
        Real.exp rho ^ 4 := by
      exact mul_le_mul hweighted hopposite (norm_nonneg _)
        (mul_nonneg (pow_nonneg hstripNonneg 4)
          (cmp89Eq251MultidimensionalAliasWeight_nonneg 1 m))
    _ = cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
        Real.exp rho ^ 4 *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by ring

/-- Before redistribution, the complex noncentral quotient is controlled by
one reciprocal-alias weight and the exact radial factor `|q|_2^(-2)`. -/
theorem norm_cmp89Eq248ComplexAliasDenominatorSummand_le_radialWeight
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAveragePair 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq249ComplexNoncentralAliasRadialConstant rho *
        (cmp89Eq251EuclideanNorm
            (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) ^
              ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
  let q : Fin 4 → ℝ :=
    fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m
  have haliasReal : ∀ mu, (aliasZ mu).re = q mu := by
    intro mu
    simp [aliasZ, q, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal mu]
  have haliasImag : ∀ mu, |(aliasZ mu).im| ≤ rho := by
    intro mu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag mu
  have hpair :
      ‖cmp89Eq245EntireAveragePair 4 N aliasZ‖ ≤
        cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
          Real.exp rho ^ 4 *
          cmp89Eq251MultidimensionalAliasWeight 1 m :=
    norm_cmp89Eq245EntireAveragePair_scaled_alias_le
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
  have hstripNonneg :
      0 ≤ cmp89Eq245EntireAverageAliasStripConstant rho := by
    rw [cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpower :
      cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) =
        (cmp89Eq251MomentumSquare q)⁻¹ := by
    rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
      Real.rpow_neg hqNorm.le, Real.rpow_two,
      sq_cmp89Eq251EuclideanNorm]
  have hgapInv :
      (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ =
        2 * (3 * Real.pi) ^ 2 *
          (cmp89Eq251MomentumSquare q)⁻¹ := by
    field_simp [Real.pi_ne_zero, ne_of_gt hqSquare]
  rw [show cmp89Eq248EntireAliasMomentum z m = aliasZ by rfl,
    norm_div, div_eq_mul_inv]
  calc
    ‖cmp89Eq245EntireAveragePair 4 N aliasZ‖ *
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖⁻¹ ≤
      (cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
          Real.exp rho ^ 4 *
          cmp89Eq251MultidimensionalAliasWeight 1 m) *
        (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
      exact mul_le_mul hpair hdenInv (inv_nonneg.mpr (norm_nonneg _))
        (mul_nonneg
          (mul_nonneg (pow_nonneg hstripNonneg 4)
            (pow_nonneg (Real.exp_pos rho).le 4))
          (cmp89Eq251MultidimensionalAliasWeight_nonneg 1 m))
    _ = cmp89Eq249ComplexNoncentralAliasRadialConstant rho *
        (cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
      rw [hgapInv, hpower,
        cmp89Eq249ComplexNoncentralAliasRadialConstant]
      ring

/-- Final pointwise source-weight bound for one noncentral complex alias
quotient.  The exponent is the literal CMP89 (2.51) exponent at
`alpha = -1`, hence is strictly summable in every positive dimension. -/
theorem norm_cmp89Eq248ComplexAliasDenominatorSummand_le_sourceWeight
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAveragePair 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq249ComplexNoncentralAliasQuotientConstant rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
  let q : Fin 4 → ℝ :=
    fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  have hradial :=
    norm_cmp89Eq248ComplexAliasDenominatorSummand_le_radialWeight
      (mass := mass) hN hrho hradius hm hm0 hp hreal himag hamplitude
  have hredistribute :
      cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - (-1 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
    exact cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
      (d := 4) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num) hm0 hp
  have hradialConstant :
      0 ≤ cmp89Eq249ComplexNoncentralAliasRadialConstant rho := by
    rw [cmp89Eq249ComplexNoncentralAliasRadialConstant,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  calc
    ‖cmp89Eq245EntireAveragePair 4 N
          (cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq249ComplexNoncentralAliasRadialConstant rho *
        (cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
      simpa only [q] using hradial
    _ ≤ cmp89Eq249ComplexNoncentralAliasRadialConstant rho *
        (3 ^ (1 - (-1 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m) := by
      exact mul_le_mul_of_nonneg_left hredistribute
        hradialConstant
    _ = cmp89Eq249ComplexNoncentralAliasQuotientConstant rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
      rw [cmp89Eq249ComplexNoncentralAliasQuotientConstant]
      ring

end

end YangMills.RG
