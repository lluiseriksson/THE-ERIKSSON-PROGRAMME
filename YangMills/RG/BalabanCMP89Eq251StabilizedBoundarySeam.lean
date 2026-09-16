/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251CommonStripHolomorphy
import YangMills.RG.BalabanCMP89Eq251DisplayedIntegrandPeriodicity

/-!
# Physical Brillouin-face seam for the stabilized CMP89 integrand

The stabilized extension is not globally postulated periodic.  On the lower
Brillouin face `p nu = -pi`, this module derives the complete non-singular
domain of the printed rational formula: every fine symbol, the unit symbol
and the reduced denominator.  The zero alias receives its positive momentum
gap from the boundary coordinate itself; nonzero aliases use the already
sealed radial gap.  The reduced denominator is recovered from the exact
identity `centralFine * reduced = stabilized`.

Only after constructing that literal domain do we use the sealed displayed
period and transfer it back to the stabilized extension.  This produces the
boundary seam consumed by the generic rectangular Cauchy theorem without a
global stabilized-periodicity assumption.

No contour integral, complete strip bound `B0`, Fourier/physical rate
dictionary or window-15 attainment is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- On a Brillouin face, every fine symbol in the full centered alias fibre is
nonzero.  The central alias uses the face coordinate rather than a nonzero
alias hypothesis. -/
theorem cmp89Eq251FineSymbol_ne_zero_of_boundaryFace
    {L j : ℕ} [NeZero L] {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (nu : Fin 4) {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j))
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
        (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
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
  have hqRadius : Real.pi ≤ cmp89Eq251EuclideanNorm q := by
    by_cases hm0 : m = 0
    · have hqNu : q nu = -Real.pi := by
        simp [q, hm0, hface]
      calc
        Real.pi = |q nu| := by rw [hqNu]; simp [abs_of_pos Real.pi_pos]
        _ ≤ cmp89Eq251EuclideanNorm q :=
          abs_le_cmp89Eq251EuclideanNorm q nu
    · exact pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp
  have hbudget :
      cmp89Eq249NoncentralComplexGapBudget rho q ≤
        ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2 :=
    cmp89Eq249NoncentralComplexGapBudget_le_of_uniformRadiusCondition
      hrho hradius hqRadius
  have hlower :
      ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2 ≤
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 ((L ^ j : ℕ) : ℝ)⁻¹ mass aliasZ‖ := by
    exact half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol
      hN hrho hm hp haliasReal haliasImag (by simpa [q] using hbudget)
  have hqPos : 0 < cmp89Eq251EuclideanNorm q :=
    Real.pi_pos.trans_le hqRadius
  have hmomentumPos : 0 < cmp89Eq251MomentumSquare q := by
    rw [← sq_cmp89Eq251EuclideanNorm]
    positivity
  have hgapPos :
      0 < ((1 / (3 * Real.pi)) ^ 2 *
        cmp89Eq251MomentumSquare q) / 2 := by positivity
  apply norm_pos_iff.mp
  simpa [aliasZ, Nat.cast_pow] using hgapPos.trans_le hlower

/-- The common strip budgets construct the full domain of the original
displayed rational integrand on one lower Brillouin face. -/
theorem cmp89Eq251DisplayedDomain_of_boundaryFace
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    cmp89Eq249EntireUnitLaplacianSymbol 4 mass z ≠ 0 ∧
      cmp89Eq247ComplexReducedAliasDenominator 4 L j mass a z ≠ 0 ∧
      ∀ m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j),
        cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
  have hfine : ∀ m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j),
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) ≠ 0 := by
    intro m hm
    exact cmp89Eq251FineSymbol_ne_zero_of_boundaryFace
      hrho hradius nu hm hp hface hreal himag
  have hcentral :
      cmp89Eq249CentralEntireFineSymbol 4 L j mass z ≠ 0 := by
    have h := hfine (cmp89Eq249ZeroAlias 4)
      (cmp89Eq249ZeroAlias_mem 4 L j)
    simpa [cmp89Eq249CentralEntireFineSymbol,
      cmp89Eq248EntireAliasMomentum_zero] using h
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero
      ha hmassPos hrho hradius hmass hwindow hp hreal himag hamplitude
  have hreduced :
      cmp89Eq247ComplexReducedAliasDenominator 4 L j mass a z ≠ 0 := by
    intro hreducedZero
    apply hstabilized
    rw [← cmp89Eq249CentralFine_mul_reduced_eq_stabilized
      4 L j mass a z hcentral, hreducedZero, mul_zero]
  have hunitFine :
      cmp89Eq245EntireScaledLaplacianSymbol 4 (((1 : ℝ) ^ 0)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias 4)) ≠ 0 :=
    cmp89Eq251FineSymbol_ne_zero_of_boundaryFace
      (L := 1) (j := 0) hrho hradius nu
        (cmp89Eq249ZeroAlias_mem 4 1 0) hp hface hreal himag
  have hunit : cmp89Eq249EntireUnitLaplacianSymbol 4 mass z ≠ 0 := by
    simpa [cmp89Eq249EntireUnitLaplacianSymbol,
      cmp89Eq248EntireAliasMomentum_zero] using hunitFine
  exact ⟨hunit, hreduced, hfine⟩

/-- The two vertical Brillouin faces agree for the stabilized extension.  All
non-singularity needed to pass through the displayed formula is constructed
from the common strip budgets at the lower face. -/
theorem cmp89Eq251ComplexStabilizedIntegrand_boundarySeam
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu mu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (holderU transportU : Fin 4 → ℤ) :
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) =
      cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU) := by
  rcases cmp89Eq251DisplayedDomain_of_boundaryFace
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass nu hp hface
        hreal himag with
    ⟨hunit, hreduced, hfine⟩
  exact cmp89Eq251ComplexStabilizedIntegrand_physicalPeriodShift_of_nonzero
    nu mu holderU transportU hunit hreduced hfine

end

end YangMills.RG
