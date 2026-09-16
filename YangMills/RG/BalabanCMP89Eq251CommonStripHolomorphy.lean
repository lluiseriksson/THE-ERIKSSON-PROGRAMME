/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedIntegrandHolomorphy

/-!
# Common-strip holomorphy of the stabilized CMP89 integrand

Cold validation: exact source checkpoint
`44e68aee0ec5910738068ee4188a6bbbfd00e4bd` passed GitHub Actions run
`31287808567` with `.lake/build` restore and save both skipped. The focal
completed 8,444 jobs and all three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The already sealed scalar-radius theorem supplies one positive `rho` for the
amplitude, noncentral-gap and stabilized-denominator budgets simultaneously.
This module turns those scalar facts into exactly the two nonvanishing inputs
of the stabilized integrand and hence into pointwise complex differentiability
throughout the literal four-dimensional strip.

No nonvanishing condition is reintroduced for the unit symbol, reduced
denominator or central fine symbol: those factors were cancelled before the
stabilized integrand was defined.  The flowing source conditions `0 < mass`
and `mass^2 <= 1` remain explicit inputs.  Boundary-seam equality, iterated
contour displacement, a uniform integrand bound `B0`, the Fourier/physical
rate dictionary and window-15 attainment remain separate.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Every noncentral fine symbol occurring literally in the stabilized
integrand is nonzero throughout the common scalar strip. -/
theorem cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
      (cmp89Eq249ZeroAlias 4))
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hm0 : m ≠ cmp89Eq249ZeroAlias 4 := (Finset.mem_erase.mp hm).1
  have hmMem : m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j) :=
    (Finset.mem_erase.mp hm).2
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m
  have haliasReal : ∀ mu,
      (aliasZ mu).re = p mu + 2 * Real.pi * (m mu : ℝ) := by
    intro mu
    simp [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal mu]
  have haliasImag : ∀ mu, |(aliasZ mu).im| ≤ rho := by
    intro mu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag mu
  have hpositive :
      0 < ‖cmp89Eq245EntireScaledLaplacianSymbol
        4 ((L ^ j : ℕ) : ℝ)⁻¹ mass aliasZ‖ := by
    apply norm_cmp89Eq245EntireScaledLaplacianSymbol_noncentral_pos
      hN hrho hmMem hm0 hp haliasReal haliasImag
    exact cmp89Eq249NoncentralComplexGapBudget_le_of_uniformRadiusCondition
      hrho hradius (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)
  apply norm_pos_iff.mp
  simpa [aliasZ, Nat.cast_pow] using hpositive

/-- The three scalar strip conditions discharge both surviving denominator
families and make the stabilized integrand differentiable at every point of
the common strip. -/
theorem differentiableAt_cmp89Eq251ComplexStabilizedIntegrand_of_commonRadius
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    {mu : Fin 4}
    {holderDisplacement transportDisplacement : Fin 4 → ℝ} :
    DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha w mu
        holderDisplacement transportDisplacement) z := by
  have hfine : ∀ m ∈
      (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
        (cmp89Eq249ZeroAlias 4),
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
    intro m hm
    exact cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
      hrho hradius hm hp hreal himag
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero
      ha hmassPos hrho hradius hmass hwindow hp hreal himag hamplitude
  exact differentiableAt_cmp89Eq251ComplexStabilizedIntegrand
    hfine hstabilized

/-- For positive averaging coefficient and a flowing mass inside the printed
mass window, one positive radius satisfies all three scalar budgets and makes
the stabilized integrand holomorphic throughout the corresponding strip. -/
theorem exists_cmp89Eq251ComplexStabilizedIntegrand_commonStripHolomorphy
    {L j : ℕ} [NeZero L] {mass a alpha : ℝ}
    (ha : 0 < a) (hmassPos : 0 < mass)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {mu : Fin 4}
    {holderDisplacement transportDisplacement : Fin 4 → ℝ} :
    ∃ rho : ℝ, 0 < rho ∧
      rho * Real.exp rho ≤ 1 / 6 ∧
      CMP89Eq249UniformNoncentralComplexRadiusCondition rho ∧
      CMP89Eq249CentralStabilizedComplexWindow a rho ∧
      ∀ (p : Fin 4 → ℝ), (∀ nu, |p nu| ≤ Real.pi) →
        ∀ (z : Fin 4 → ℂ), (∀ nu, (z nu).re = p nu) →
          (∀ nu, |(z nu).im| ≤ rho) →
            DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
              cmp89Eq251ComplexStabilizedIntegrand
                4 L j mass a alpha w mu holderDisplacement
                  transportDisplacement) z := by
  rcases exists_cmp89Eq249CentralStabilizedComplexRadius ha with
    ⟨rho, hrho, hamplitude, hradius, hwindow⟩
  refine ⟨rho, hrho, hamplitude, hradius, hwindow, ?_⟩
  intro p hp z hreal himag
  exact differentiableAt_cmp89Eq251ComplexStabilizedIntegrand_of_commonRadius
    ha.le hmassPos hrho.le hamplitude hradius hwindow hmass
      hp hreal himag

end

end YangMills.RG
