/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq250FullDenominatorLower
import YangMills.RG.BalabanCMP89Eq251AliasWeightRedistribution

/-!
# Cold-sealed noncentral real integrand in CMP89 (2.51)

Cold GitHub Actions run `31238106632` compiler-verified source checkpoint
`83272ce580198092dcc516c34e2a353a1bee42b8` with workflow checkpoint
`eb27ce65d6b3c451da33821c5bdcfdb889f53277`. Both restore and save of
`.lake/build` were skipped; the warning-free focal and audit exited zero, the
build closed at 3289 jobs, and all four audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

This module composes the five literal factors in the noncentral summand of
CMP89 (2.51): the Holder phase quotient, the inverse complete denominator,
the scaled derivative, the complex averaging amplitude and the massive-symbol
ratio.  Their already sealed estimates give the exact product weight printed
on p. 586, with every constant visible.

The central alias is deliberately excluded by `m ≠ 0`; it is the separate
`O(1)` term in the source.  This module does not sum aliases, construct the
analytic strip or identify the Fourier kernel with the regional Green.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal real majorand of one noncentral summand in CMP89 (2.51).
The division by the displacement weight has already been exposed, but none
of the five source factors has been replaced by a free bound. -/
def cmp89Eq251NoncentralRealIntegrand
    (d L j : ℕ) (mass a alpha : ℝ) (p : Fin d → ℝ)
    (m : Fin d → ℤ) (mu : Fin d) (displacement : Fin d → ℝ) : ℝ :=
  let q : Fin d → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  (‖Complex.exp (Complex.I * cmp89Eq251Phase q displacement) - 1‖ /
      cmp89Eq251EuclideanNorm displacement ^ alpha) *
    (1 / cmp89Eq250FullAliasDenominator d L j mass a p) *
    cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (q mu) *
    ‖cmp89Eq245ComplexAverageAmplitude d (((L : ℝ) ^ j)⁻¹) q‖ *
    (cmp89Eq249UnitLaplacianSymbol d mass p /
      cmp89Eq245ScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass q)

/-- The completely explicit dimension/source constant multiplying the
summable noncentral product weight in (2.51). -/
def cmp89Eq251NoncentralRealIntegrandConstant
    (d : ℕ) (a alpha : ℝ) : ℝ :=
  2 * (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ *
    (18 * Real.pi) ^ d *
    ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) *
    3 ^ (1 - alpha)

/-- The Euclidean norm used in (2.51) squares to the literal momentum square. -/
theorem sq_cmp89Eq251EuclideanNorm
    {d : ℕ} (q : Fin d → ℝ) :
    cmp89Eq251EuclideanNorm q ^ 2 = cmp89Eq251MomentumSquare q := by
  rw [cmp89Eq251EuclideanNorm]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Literal noncentral integrand estimate in CMP89 (2.51).  The mass window
is kept as a named flowing-quantity hypothesis; no claim that RG dynamics
preserves it is made here. -/
theorem cmp89Eq251NoncentralRealIntegrand_le_sourceWeight
    {d L j : ℕ} [NeZero L] (hd : 0 < d)
    {mass a alpha : ℝ} (hmass : 0 < mass)
    (hmassWindow : CMP89Eq251UniformMassWindow mass) (ha : 0 < a)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {m : Fin d → ℤ} (hm : m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j))
    (hm0 : m ≠ 0) (mu : Fin d) {displacement : Fin d → ℝ}
    (hdisplacement : 0 < cmp89Eq251EuclideanNorm displacement) :
    cmp89Eq251NoncentralRealIntegrand
        d L j mass a alpha p m mu displacement ≤
      cmp89Eq251NoncentralRealIntegrandConstant d a alpha *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent d alpha) m := by
  let q : Fin d → ℝ :=
    fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  have hN : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hxi : 0 < ((L : ℝ) ^ j)⁻¹ :=
    (cmp89Eq245_inverseScale_mem_Ioc L j).1
  have hqPos : 0 < cmp89Eq251EuclideanNorm q := by
    exact Real.pi_pos.trans_le
      (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)
  have hphase :=
    norm_cmp89Eq251_phaseFactor_div_displacement_rpow_le
      halpha0 halpha1 q displacement hdisplacement
  have hdenLower :=
    cmp89Eq250CentralAliasLowerConstant_le_full_denominator
      (d := d) (L := L) (j := j) (mass := mass) (a := a) (p := p)
      ha.le hmass hp
  have hcentralPos : 0 < cmp89Eq250CentralAliasLowerConstant d a :=
    cmp89Eq250CentralAliasLowerConstant_pos ha
  have hdenInv :
      1 / cmp89Eq250FullAliasDenominator d L j mass a p ≤
        (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ := by
    simpa [one_div] using
      one_div_le_one_div_of_le hcentralPos hdenLower
  have hderivative :
      cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (q mu) ≤
        cmp89Eq251EuclideanNorm q :=
    (cmp89Eq245ScaledDifferenceNorm_le_abs hxi).trans
      (abs_le_cmp89Eq251EuclideanNorm q mu)
  have hamplitude :
      ‖cmp89Eq245ComplexAverageAmplitude
          d (((L : ℝ) ^ j)⁻¹) q‖ ≤
        (18 * Real.pi) ^ d *
          cmp89Eq251MultidimensionalAliasWeight 1 m := by
    simpa only [q, Nat.cast_pow] using
      norm_cmp89Eq245ComplexAverageAmplitude_scaled_alias_le hN hm hp
  have hratio :
      cmp89Eq249UnitLaplacianSymbol d mass p /
          cmp89Eq245ScaledLaplacianSymbol
            d (((L : ℝ) ^ j)⁻¹) mass q ≤
        ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) /
          cmp89Eq251MomentumSquare q := by
    simpa only [q, Nat.cast_pow] using
      cmp89Eq249_unit_div_scaled_noncentral_alias_le
        hN hmassWindow hm hm0 hp
  have hnormSquare :
      cmp89Eq251EuclideanNorm q ^ 2 = cmp89Eq251MomentumSquare q :=
    sq_cmp89Eq251EuclideanNorm q
  have hradial :
      cmp89Eq251EuclideanNorm q ^ alpha *
          cmp89Eq251EuclideanNorm q /
          cmp89Eq251MomentumSquare q =
        cmp89Eq251EuclideanNorm q ^ (alpha - 1) := by
    rw [← hnormSquare, Real.rpow_sub_one hqPos.ne']
    field_simp [hqPos.ne']
  have hredistribute :
      cmp89Eq251EuclideanNorm q ^ (alpha - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - alpha) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent d alpha) m := by
    simpa only [q] using
      cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
        hd halpha1 hm0 hp
  have hfullDenPos :
      0 < cmp89Eq250FullAliasDenominator d L j mass a p :=
    hcentralPos.trans_le hdenLower
  have hdenFactorNonneg :
      0 ≤ 1 / cmp89Eq250FullAliasDenominator d L j mass a p :=
    div_nonneg (by norm_num) hfullDenPos.le
  have hderivativeNonneg :
      0 ≤ cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (q mu) := by
    rw [cmp89Eq245ScaledDifferenceNorm]
    exact norm_nonneg _
  have hamplitudeNonneg :
      0 ≤ ‖cmp89Eq245ComplexAverageAmplitude
        d (((L : ℝ) ^ j)⁻¹) q‖ := norm_nonneg _
  have hunitNonneg : 0 ≤ cmp89Eq249UnitLaplacianSymbol d mass p := by
    rw [cmp89Eq249UnitLaplacianSymbol]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hscaledPos :
      0 < cmp89Eq245ScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass q := by
    rw [cmp89Eq245ScaledLaplacianSymbol]
    exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_pos hmass 2)
  have hratioNonneg :
      0 ≤ cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass q :=
    div_nonneg hunitNonneg hscaledPos.le
  have hphaseBoundNonneg :
      0 ≤ 2 * cmp89Eq251EuclideanNorm q ^ alpha := by positivity
  have hdenBoundNonneg :
      0 ≤ (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ := by positivity
  have hderivativeBoundNonneg :
      0 ≤ cmp89Eq251EuclideanNorm q :=
    cmp89Eq251EuclideanNorm_nonneg q
  have hamplitudeBoundNonneg :
      0 ≤ (18 * Real.pi) ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m :=
    mul_nonneg (pow_nonneg (by positivity) d)
      (cmp89Eq251MultidimensionalAliasWeight_nonneg 1 m)
  have hmomentumPos : 0 < cmp89Eq251MomentumSquare q := by
    rw [← hnormSquare]
    positivity
  have h12 :
      (‖Complex.exp
            (Complex.I * cmp89Eq251Phase q displacement) - 1‖ /
          cmp89Eq251EuclideanNorm displacement ^ alpha) *
          (1 / cmp89Eq250FullAliasDenominator d L j mass a p) ≤
        (2 * cmp89Eq251EuclideanNorm q ^ alpha) *
          (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ :=
    mul_le_mul hphase hdenInv hdenFactorNonneg hphaseBoundNonneg
  have h123 :
      ((‖Complex.exp
              (Complex.I * cmp89Eq251Phase q displacement) - 1‖ /
            cmp89Eq251EuclideanNorm displacement ^ alpha) *
            (1 / cmp89Eq250FullAliasDenominator d L j mass a p)) *
          cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (q mu) ≤
        ((2 * cmp89Eq251EuclideanNorm q ^ alpha) *
            (cmp89Eq250CentralAliasLowerConstant d a)⁻¹) *
          cmp89Eq251EuclideanNorm q :=
    mul_le_mul h12 hderivative hderivativeNonneg
      (mul_nonneg hphaseBoundNonneg hdenBoundNonneg)
  have h1234 :
      (((‖Complex.exp
                (Complex.I * cmp89Eq251Phase q displacement) - 1‖ /
              cmp89Eq251EuclideanNorm displacement ^ alpha) *
              (1 / cmp89Eq250FullAliasDenominator d L j mass a p)) *
            cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (q mu)) *
          ‖cmp89Eq245ComplexAverageAmplitude
            d (((L : ℝ) ^ j)⁻¹) q‖ ≤
        (((2 * cmp89Eq251EuclideanNorm q ^ alpha) *
              (cmp89Eq250CentralAliasLowerConstant d a)⁻¹) *
            cmp89Eq251EuclideanNorm q) *
          ((18 * Real.pi) ^ d *
            cmp89Eq251MultidimensionalAliasWeight 1 m) :=
    mul_le_mul h123 hamplitude hamplitudeNonneg
      (mul_nonneg
        (mul_nonneg hphaseBoundNonneg hdenBoundNonneg)
        hderivativeBoundNonneg)
  have hproduct :
      ((((‖Complex.exp
                  (Complex.I * cmp89Eq251Phase q displacement) - 1‖ /
                cmp89Eq251EuclideanNorm displacement ^ alpha) *
                (1 / cmp89Eq250FullAliasDenominator d L j mass a p)) *
              cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (q mu)) *
            ‖cmp89Eq245ComplexAverageAmplitude
              d (((L : ℝ) ^ j)⁻¹) q‖) *
          (cmp89Eq249UnitLaplacianSymbol d mass p /
            cmp89Eq245ScaledLaplacianSymbol
              d (((L : ℝ) ^ j)⁻¹) mass q) ≤
        ((((2 * cmp89Eq251EuclideanNorm q ^ alpha) *
                (cmp89Eq250CentralAliasLowerConstant d a)⁻¹) *
              cmp89Eq251EuclideanNorm q) *
            ((18 * Real.pi) ^ d *
              cmp89Eq251MultidimensionalAliasWeight 1 m)) *
          (((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) /
            cmp89Eq251MomentumSquare q) :=
    mul_le_mul h1234 hratio hratioNonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hphaseBoundNonneg hdenBoundNonneg)
          hderivativeBoundNonneg)
        hamplitudeBoundNonneg)
  have hconstantNonneg :
      0 ≤ 2 * (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ *
        (18 * Real.pi) ^ d *
        ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) := by
    positivity
  rw [cmp89Eq251NoncentralRealIntegrand,
    cmp89Eq251NoncentralRealIntegrandConstant]
  dsimp only [q]
  calc
    (‖Complex.exp
          (Complex.I * cmp89Eq251Phase q displacement) - 1‖ /
          cmp89Eq251EuclideanNorm displacement ^ alpha) *
        (1 / cmp89Eq250FullAliasDenominator d L j mass a p) *
        cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (q mu) *
        ‖cmp89Eq245ComplexAverageAmplitude d (((L : ℝ) ^ j)⁻¹) q‖ *
        (cmp89Eq249UnitLaplacianSymbol d mass p /
          cmp89Eq245ScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass q) ≤
      (2 * cmp89Eq251EuclideanNorm q ^ alpha) *
        (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ *
        cmp89Eq251EuclideanNorm q *
        ((18 * Real.pi) ^ d *
          cmp89Eq251MultidimensionalAliasWeight 1 m) *
        (((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) /
          cmp89Eq251MomentumSquare q) := hproduct
    _ =
      (2 * (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ *
          (18 * Real.pi) ^ d *
          ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1))) *
        (cmp89Eq251EuclideanNorm q ^ (alpha - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := by
      rw [← hradial]
      ring
    _ ≤
      (2 * (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ *
          (18 * Real.pi) ^ d *
          ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1))) *
        (3 ^ (1 - alpha) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent d alpha) m) :=
      mul_le_mul_of_nonneg_left hredistribute hconstantNonneg
    _ =
      2 * (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ *
          (18 * Real.pi) ^ d *
          ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) *
          3 ^ (1 - alpha) *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent d alpha) m := by
      ring

end

end YangMills.RG
