/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251NoncentralRealIntegrandBound

/-!
# PRE-VALIDATION: central real integrand in CMP89 (2.51)

The source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

CMP89 p. 586 separates the zero reciprocal alias as an `O(1)` term.  This
module constructs that literal branch from the same five-factor integrand as
the sealed noncentral theorem and proves a momentum-uniform explicit bound on
the central Brillouin cube.  It does not use the noncentral mass window.

No alias sum, analytic strip or physical Green transport is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Uniform Euclidean radius of the central Brillouin cube in dimension `d`. -/
def cmp89Eq251CentralMomentumRadius (d : ℕ) : ℝ :=
  Real.sqrt ((d : ℝ) * Real.pi ^ 2)

/-- The literal zero-alias branch of the real integrand in CMP89 (2.51). -/
def cmp89Eq251CentralRealIntegrand
    (d L j : ℕ) (mass a alpha : ℝ) (p : Fin d → ℝ)
    (mu : Fin d) (displacement : Fin d → ℝ) : ℝ :=
  cmp89Eq251NoncentralRealIntegrand d L j mass a alpha p
    (fun _ => 0) mu displacement

/-- Explicit `O(1)` constant for the central branch in (2.51). -/
def cmp89Eq251CentralRealIntegrandConstant (d : ℕ) (a : ℝ) : ℝ :=
  2 * (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ *
    (1 + cmp89Eq251CentralMomentumRadius d) *
    cmp89Eq251CentralMomentumRadius d *
    (18 * Real.pi) ^ d * (3 * Real.pi) ^ 2

/-- The literal momentum square is uniformly bounded on the central
Brillouin cube. -/
theorem cmp89Eq251MomentumSquare_le_central_radius_sq
    {d : ℕ} {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq251MomentumSquare p ≤ (d : ℝ) * Real.pi ^ 2 := by
  rw [cmp89Eq251MomentumSquare]
  calc
    (∑ mu, p mu ^ 2) ≤ ∑ _mu : Fin d, Real.pi ^ 2 := by
      apply Finset.sum_le_sum
      intro mu _
      rw [← sq_abs (p mu), ← sq_abs Real.pi]
      exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2
        (by simpa [abs_of_pos Real.pi_pos] using hp mu)
    _ = (d : ℝ) * Real.pi ^ 2 := by
      rw [Fin.sum_const, nsmul_eq_mul]

/-- Euclidean form of the same central-cube radius bound. -/
theorem cmp89Eq251EuclideanNorm_le_central_radius
    {d : ℕ} {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq251EuclideanNorm p ≤ cmp89Eq251CentralMomentumRadius d := by
  rw [cmp89Eq251EuclideanNorm, cmp89Eq251CentralMomentumRadius]
  exact Real.sqrt_le_sqrt
    (cmp89Eq251MomentumSquare_le_central_radius_sq hp)

/-- For exponents in `[0,1]`, the radial Holder factor is bounded by
`1+x` without a lower bound on `x`. -/
theorem rpow_le_one_add_self_of_mem_Icc
    {x alpha : ℝ} (hx : 0 ≤ x) (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha ≤ 1) :
    x ^ alpha ≤ 1 + x := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 halpha0).trans (by linarith)
  · have h1x : 1 ≤ x := (lt_of_not_ge hx1).le
    exact (Real.rpow_le_self_of_one_le h1x halpha1).trans (by linarith)

/-- On the central alias, the massive-symbol ratio is uniformly bounded by
the explicit source comparison constant `(3*pi)^2`. -/
theorem cmp89Eq249_unit_div_scaled_central_alias_le
    {d L j : ℕ} [NeZero L] {mass : ℝ} (hmass : 0 < mass)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass p ≤
      (3 * Real.pi) ^ 2 := by
  obtain ⟨hxi, hxi1⟩ := cmp89Eq245_inverseScale_mem_Ioc L j
  have hzone :
      ∀ mu, |((L : ℝ) ^ j)⁻¹ * p mu| ≤ 3 * Real.pi / 2 := by
    intro mu
    rw [abs_mul, abs_of_pos hxi]
    have hmul : ((L : ℝ) ^ j)⁻¹ * |p mu| ≤ Real.pi := by
      calc
        ((L : ℝ) ^ j)⁻¹ * |p mu| ≤ 1 * Real.pi :=
          mul_le_mul hxi1 (hp mu) (abs_nonneg _) (by norm_num)
        _ = Real.pi := one_mul _
    nlinarith [Real.pi_pos]
  have hden : 0 < cmp89Eq251MomentumSquare p + mass ^ 2 :=
    add_pos_of_nonneg_of_pos
      (cmp89Eq251MomentumSquare_nonneg p) (pow_pos hmass 2)
  have hratio := cmp89Eq249_unit_div_scaled_le_momentum_ratio
    (d := d) (xi := ((L : ℝ) ^ j)⁻¹) (mass := mass)
    (p := p) (q := p) hxi hzone hden
  calc
    cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass p ≤
      (3 * Real.pi) ^ 2 *
        (cmp89Eq251MomentumSquare p + mass ^ 2) /
          (cmp89Eq251MomentumSquare p + mass ^ 2) := hratio
    _ = (3 * Real.pi) ^ 2 := by field_simp [hden.ne']

/-- Literal central `O(1)` integrand estimate from CMP89 (2.51). -/
theorem cmp89Eq251CentralRealIntegrand_le_constant
    {d L j : ℕ} [NeZero L] {mass a alpha : ℝ}
    (hmass : 0 < mass) (ha : 0 < a)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (mu : Fin d) {displacement : Fin d → ℝ}
    (hdisplacement : 0 < cmp89Eq251EuclideanNorm displacement) :
    cmp89Eq251CentralRealIntegrand
        d L j mass a alpha p mu displacement ≤
      cmp89Eq251CentralRealIntegrandConstant d a := by
  let zeroAlias : Fin d → ℤ := fun _ => 0
  have hN : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hzero :
      zeroAlias ∈ cmp89Eq245CenteredAliasVectors d (L ^ j) :=
    zero_mem_cmp89Eq245CenteredAliasVectors_pow d L j
  have hxi : 0 < ((L : ℝ) ^ j)⁻¹ :=
    (cmp89Eq245_inverseScale_mem_Ioc L j).1
  have hphaseRaw :=
    norm_cmp89Eq251_phaseFactor_div_displacement_rpow_le
      halpha0 halpha1 p displacement hdisplacement
  have hrpow :
      cmp89Eq251EuclideanNorm p ^ alpha ≤
        1 + cmp89Eq251EuclideanNorm p :=
    rpow_le_one_add_self_of_mem_Icc
      (cmp89Eq251EuclideanNorm_nonneg p) halpha0 halpha1
  have hradius := cmp89Eq251EuclideanNorm_le_central_radius hp
  have hphase :
      ‖Complex.exp (Complex.I * cmp89Eq251Phase p displacement) - 1‖ /
          cmp89Eq251EuclideanNorm displacement ^ alpha ≤
        2 * (1 + cmp89Eq251CentralMomentumRadius d) :=
    calc
      ‖Complex.exp (Complex.I * cmp89Eq251Phase p displacement) - 1‖ /
          cmp89Eq251EuclideanNorm displacement ^ alpha ≤
        2 * cmp89Eq251EuclideanNorm p ^ alpha := hphaseRaw
      _ ≤ 2 * (1 + cmp89Eq251EuclideanNorm p) :=
        mul_le_mul_of_nonneg_left hrpow (by norm_num)
      _ ≤ 2 * (1 + cmp89Eq251CentralMomentumRadius d) := by
        gcongr
  have hdenLower :=
    cmp89Eq250CentralAliasLowerConstant_le_full_denominator
      (d := d) (L := L) (j := j) (mass := mass) (a := a) (p := p)
      ha.le hmass hp
  have hcentralPos : 0 < cmp89Eq250CentralAliasLowerConstant d a :=
    cmp89Eq250CentralAliasLowerConstant_pos ha
  have hfullDenPos :
      0 < cmp89Eq250FullAliasDenominator d L j mass a p :=
    hcentralPos.trans_le hdenLower
  have hdenInv :
      1 / cmp89Eq250FullAliasDenominator d L j mass a p ≤
        (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ := by
    simpa [one_div] using
      one_div_le_one_div_of_le hcentralPos hdenLower
  have hderivative :
      cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (p mu) ≤
        cmp89Eq251CentralMomentumRadius d :=
    (cmp89Eq245ScaledDifferenceNorm_le_abs hxi).trans
      ((abs_le_cmp89Eq251EuclideanNorm p mu).trans hradius)
  have hamplitude :
      ‖cmp89Eq245ComplexAverageAmplitude
          d (((L : ℝ) ^ j)⁻¹) p‖ ≤
        (18 * Real.pi) ^ d := by
    have h := norm_cmp89Eq245ComplexAverageAmplitude_scaled_alias_le
      hN hzero hp
    have hweight :
        cmp89Eq251MultidimensionalAliasWeight 1 zeroAlias = 1 := by
      simp [cmp89Eq251MultidimensionalAliasWeight,
        cmp89Eq251OneDimensionalAliasWeight, zeroAlias]
    calc
      ‖cmp89Eq245ComplexAverageAmplitude
          d (((L : ℝ) ^ j)⁻¹) p‖ =
        ‖cmp89Eq245ComplexAverageAmplitude
          d (((L : ℝ) ^ j)⁻¹) (fun mu => p mu)‖ := rfl
      _ ≤ (18 * Real.pi) ^ d *
          cmp89Eq251MultidimensionalAliasWeight 1 zeroAlias := by
        simpa only [zeroAlias, Nat.cast_pow] using h
      _ = (18 * Real.pi) ^ d := by rw [hweight, mul_one]
  have hratio := cmp89Eq249_unit_div_scaled_central_alias_le
    (d := d) (L := L) (j := j) hmass hp
  have hdenFactorNonneg :
      0 ≤ 1 / cmp89Eq250FullAliasDenominator d L j mass a p :=
    div_nonneg (by norm_num) hfullDenPos.le
  have hderivativeNonneg :
      0 ≤ cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (p mu) := by
    rw [cmp89Eq245ScaledDifferenceNorm]
    exact norm_nonneg _
  have hamplitudeNonneg :
      0 ≤ ‖cmp89Eq245ComplexAverageAmplitude
        d (((L : ℝ) ^ j)⁻¹) p‖ := norm_nonneg _
  have hunitNonneg : 0 ≤ cmp89Eq249UnitLaplacianSymbol d mass p := by
    rw [cmp89Eq249UnitLaplacianSymbol]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hscaledPos :
      0 < cmp89Eq245ScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass p := by
    rw [cmp89Eq245ScaledLaplacianSymbol]
    exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_pos hmass 2)
  have hratioNonneg :
      0 ≤ cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass p :=
    div_nonneg hunitNonneg hscaledPos.le
  have hb1 : 0 ≤ 2 * (1 + cmp89Eq251CentralMomentumRadius d) :=
    mul_nonneg (by norm_num) (add_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hb2 : 0 ≤ (cmp89Eq250CentralAliasLowerConstant d a)⁻¹ := by positivity
  have hb3 : 0 ≤ cmp89Eq251CentralMomentumRadius d := by
    exact Real.sqrt_nonneg _
  have hb4 : 0 ≤ (18 * Real.pi) ^ d := by positivity
  have h12 := mul_le_mul hphase hdenInv hdenFactorNonneg hb1
  have h123 := mul_le_mul h12 hderivative hderivativeNonneg
    (mul_nonneg hb1 hb2)
  have h1234 := mul_le_mul h123 hamplitude hamplitudeNonneg
    (mul_nonneg (mul_nonneg hb1 hb2) hb3)
  have hproduct := mul_le_mul h1234 hratio hratioNonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hb1 hb2) hb3) hb4)
  change
    ((((‖Complex.exp
                (Complex.I * cmp89Eq251Phase p displacement) - 1‖ /
              cmp89Eq251EuclideanNorm displacement ^ alpha) *
            (1 / cmp89Eq250FullAliasDenominator d L j mass a p)) *
          cmp89Eq245ScaledDifferenceNorm (((L : ℝ) ^ j)⁻¹) (p mu)) *
        ‖cmp89Eq245ComplexAverageAmplitude
          d (((L : ℝ) ^ j)⁻¹) p‖) *
      (cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass p) ≤
      cmp89Eq251CentralRealIntegrandConstant d a
  exact hproduct.trans_eq (by
    rw [cmp89Eq251CentralRealIntegrandConstant]
    ring)

end

end YangMills.RG
