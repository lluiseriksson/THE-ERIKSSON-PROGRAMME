/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249ComplexNoncentralAliasSumVariation
import YangMills.RG.BalabanCMP89Eq251CentralRealIntegrandBound

/-!
# Vertical variation of the stabilized CMP89 (2.49) denominator

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

The stabilized denominator has three literal branches: the central fine
symbol, the central averaging pair, and their product with the noncentral
alias sum.  This module combines the already sealed vertical estimates for
those objects.  The product branch is expanded before estimation, so the
fine-symbol and alias-sum budgets remain separately visible.

The source mass window `mass^2 <= 1` is an explicit input.  No complex lower
bound, reciprocal bound `B0`, contour shift, Fourier/physical rate dictionary
or regional-Green estimate is claimed.

No optimized trigonometric gap or factor-two fine-symbol variation is used.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Uniform vertical budget for the central entire fine symbol on the
four-dimensional Brillouin cube. -/
def cmp89Eq249CentralFineSymbolVerticalBound (rho : ℝ) : ℝ :=
  4 * (rho * Real.exp rho) *
    (2 * Real.pi + rho * Real.exp rho)

/-- Uniform real-slice upper bound for the central scaled fine symbol under
the explicit source mass window. -/
def cmp89Eq249CentralFineSymbolRealBound : ℝ :=
  (Real.pi / 2) ^ 2 * (4 * Real.pi ^ 2 + 1)

/-- Vertical budget for the central opposite-momentum averaging pair. -/
def cmp89Eq249CentralAveragePairVerticalBound (rho : ℝ) : ℝ :=
  2 * (4 * (rho * Real.exp rho) * (Real.exp rho) ^ 4) *
    (Real.exp rho) ^ 4

/-- Complete vertical budget for the stabilized denominator. -/
def cmp89Eq249CentralStabilizedDenominatorVariationBound
    (a rho : ℝ) : ℝ :=
  cmp89Eq249CentralFineSymbolVerticalBound rho +
    a * cmp89Eq249CentralAveragePairVerticalBound rho +
    a *
      (cmp89Eq249CentralFineSymbolVerticalBound rho *
          cmp89Eq249ComplexNoncentralAliasSumBound rho +
        cmp89Eq249CentralFineSymbolRealBound *
          cmp89Eq249ComplexNoncentralAliasSumVariationBound rho)

/-- The coordinatewise central fine-symbol budget is uniform on the printed
real momentum cube. -/
theorem cmp89Eq245EntireScaledLaplacianVerticalBudget_le_centralBound
    {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu) :
    cmp89Eq245EntireScaledLaplacianVerticalBudget 4 rho z ≤
      cmp89Eq249CentralFineSymbolVerticalBound rho := by
  let eps : ℝ := rho * Real.exp rho
  have heps : 0 ≤ eps := by
    dsimp [eps]
    positivity
  rw [cmp89Eq245EntireScaledLaplacianVerticalBudget,
    cmp89Eq249CentralFineSymbolVerticalBound]
  change (∑ mu, eps * (2 * |(z mu).re| + eps)) ≤
    4 * eps * (2 * Real.pi + eps)
  calc
    (∑ mu, eps * (2 * |(z mu).re| + eps)) ≤
        ∑ _mu : Fin 4, eps * (2 * Real.pi + eps) := by
      apply Finset.sum_le_sum
      intro mu _
      apply mul_le_mul_of_nonneg_left _ heps
      have habs : |(z mu).re| ≤ Real.pi := by
        rw [hreal mu]
        exact hp mu
      linarith
    _ = 4 * eps * (2 * Real.pi + eps) := by
      rw [Fin.sum_const, nsmul_eq_mul]
      norm_num

/-- The real-slice central fine symbol has a scale-uniform upper bound once
the source mass window is named explicitly. -/
theorem norm_cmp89Eq249CentralEntireFineSymbol_realSlice_le
    {L j : ℕ} [NeZero L] {mass : ℝ}
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass
        (fun mu => (p mu : ℂ))‖ ≤
      cmp89Eq249CentralFineSymbolRealBound := by
  let xi : ℝ := ((L : ℝ) ^ j)⁻¹
  obtain ⟨hxi, _hxi1⟩ := cmp89Eq245_inverseScale_mem_Ioc L j
  have hscaledNonneg :
      0 ≤ cmp89Eq245ScaledLaplacianSymbol 4 xi mass p := by
    rw [cmp89Eq245ScaledLaplacianSymbol]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hcoef : 0 ≤ (Real.pi / 2) ^ 2 := sq_nonneg _
  have hscaled :=
    cmp89Eq245ScaledLaplacianSymbol_le_pi_sq_mul_unit
      (d := 4) (mass := mass) (p := p) hxi hp
  have hunit := cmp89Eq249UnitLaplacianSymbol_le_momentumSquare mass p
  have hpSquare := cmp89Eq251MomentumSquare_le_central_radius_sq hp
  have hmassSq : mass ^ 2 ≤ 1 := hmass
  have hbound :
      cmp89Eq245ScaledLaplacianSymbol 4 xi mass p ≤
        cmp89Eq249CentralFineSymbolRealBound := by
    calc
      cmp89Eq245ScaledLaplacianSymbol 4 xi mass p ≤
          (Real.pi / 2) ^ 2 *
            cmp89Eq249UnitLaplacianSymbol 4 mass p := hscaled
      _ ≤ (Real.pi / 2) ^ 2 *
            (cmp89Eq251MomentumSquare p + mass ^ 2) :=
        mul_le_mul_of_nonneg_left hunit hcoef
      _ ≤ (Real.pi / 2) ^ 2 * (4 * Real.pi ^ 2 + 1) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        exact add_le_add hpSquare hmassSq
      _ = cmp89Eq249CentralFineSymbolRealBound := rfl
  rw [cmp89Eq249CentralEntireFineSymbol,
    cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq]
  change ‖(cmp89Eq245ScaledLaplacianSymbol 4 xi mass p : ℂ)‖ ≤ _
  simpa [Complex.norm_real, abs_of_nonneg hscaledNonneg] using hbound

/-- The complete stabilized denominator varies uniformly from its matching
real slice.  Each of the three printed branches keeps its own explicit
budget. -/
theorem norm_cmp89Eq249CentralStabilizedAliasDenominator_sub_realSlice_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z -
        cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a
          (cmp89Eq245ComplexMomentumRealSlice z)‖ ≤
      cmp89Eq249CentralStabilizedDenominatorVariationBound a rho := by
  let z0 : Fin 4 → ℂ := cmp89Eq245ComplexMomentumRealSlice z
  let delta := cmp89Eq249CentralEntireFineSymbol 4 L j mass z
  let delta0 := cmp89Eq249CentralEntireFineSymbol 4 L j mass z0
  let u := cmp89Eq249CentralEntireAveragePair 4 L j z
  let u0 := cmp89Eq249CentralEntireAveragePair 4 L j z0
  let s := cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z
  let s0 := cmp89Eq249ComplexNoncentralAliasSum 4 L j mass z0
  let dV := cmp89Eq249CentralFineSymbolVerticalBound rho
  let d0B := cmp89Eq249CentralFineSymbolRealBound
  let uV := cmp89Eq249CentralAveragePairVerticalBound rho
  let sB := cmp89Eq249ComplexNoncentralAliasSumBound rho
  let sV := cmp89Eq249ComplexNoncentralAliasSumVariationBound rho
  have hN : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  obtain ⟨hxi, hxi1⟩ := cmp89Eq245_inverseScale_mem_Ioc L j
  have hz0 : z0 = fun mu => (p mu : ℂ) := by
    funext mu
    simp [z0, cmp89Eq245ComplexMomentumRealSlice, hreal mu]
  have hdeltaVar : ‖delta - delta0‖ ≤ dV := by
    have hraw :=
      norm_cmp89Eq245EntireScaledLaplacianSymbol_sub_realSlice_le
        (d := 4) (xi := ((L : ℝ) ^ j)⁻¹) (mass := mass)
        hxi hxi1 hrho himag
    have hcube :=
      cmp89Eq245EntireScaledLaplacianVerticalBudget_le_centralBound
        hrho hp hreal
    exact (by
      simpa [delta, delta0, z0, cmp89Eq249CentralEntireFineSymbol]
        using hraw).trans (by simpa [dV] using hcube)
  have hdelta0 : ‖delta0‖ ≤ d0B := by
    rw [hz0]
    simpa [delta0, d0B] using
      (norm_cmp89Eq249CentralEntireFineSymbol_realSlice_le
        (L := L) (j := j) hmass hp)
  have huVar : ‖u - u0‖ ≤ uV := by
    have hraw :=
      norm_cmp89Eq245EntireAverageAmplitude_pair_sub_realSlice_le
        (d := 4) (N := L ^ j) hN hrho himag
    simpa [u, u0, z0, cmp89Eq249CentralEntireAveragePair,
      cmp89Eq245EntireAveragePair,
      cmp89Eq249CentralAveragePairVerticalBound, uV] using hraw
  have hsBound : ‖s‖ ≤ sB := by
    simpa [s, sB] using
      (norm_cmp89Eq249ComplexNoncentralAliasSum_le_bound
        (mass := mass) hrho hradius hp hreal himag hamplitude)
  have hsVar : ‖s - s0‖ ≤ sV := by
    simpa [s, s0, z0, sV] using
      (norm_cmp89Eq249ComplexNoncentralAliasSum_sub_realSlice_le_bound
        (mass := mass) hrho hradius hp hreal himag hamplitude)
  have hrearrange :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z -
          cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z0 =
        (delta - delta0) + (a : ℂ) * (u - u0) +
          (a : ℂ) * ((delta - delta0) * s + delta0 * (s - s0)) := by
    simp only [cmp89Eq249CentralStabilizedAliasDenominator,
      delta, delta0, u, u0, s, s0]
    ring
  have haNorm : ‖(a : ℂ)‖ = a := by
    simp [Complex.norm_real, abs_of_nonneg ha]
  have huTerm : ‖(a : ℂ) * (u - u0)‖ ≤ a * uV := by
    rw [norm_mul, haNorm]
    exact mul_le_mul_of_nonneg_left huVar ha
  have hproductTerm :
      ‖(a : ℂ) * ((delta - delta0) * s + delta0 * (s - s0))‖ ≤
        a * (dV * sB + d0B * sV) := by
    rw [norm_mul, haNorm]
    calc
      a * ‖(delta - delta0) * s + delta0 * (s - s0)‖ ≤
          a * (‖(delta - delta0) * s‖ + ‖delta0 * (s - s0)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) ha
      _ = a * (‖delta - delta0‖ * ‖s‖ + ‖delta0‖ * ‖s - s0‖) := by
        rw [norm_mul, norm_mul]
      _ ≤ a * (dV * sB + d0B * sV) := by
        gcongr
  rw [show cmp89Eq245ComplexMomentumRealSlice z = z0 by rfl, hrearrange]
  calc
    ‖(delta - delta0) + (a : ℂ) * (u - u0) +
        (a : ℂ) * ((delta - delta0) * s + delta0 * (s - s0))‖ ≤
      ‖delta - delta0‖ + ‖(a : ℂ) * (u - u0)‖ +
        ‖(a : ℂ) * ((delta - delta0) * s + delta0 * (s - s0))‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_right (norm_add_le _ _) _)
    _ ≤ dV + a * uV + a * (dV * sB + d0B * sV) := by
      gcongr
    _ = cmp89Eq249CentralStabilizedDenominatorVariationBound a rho := rfl

end

end YangMills.RG
