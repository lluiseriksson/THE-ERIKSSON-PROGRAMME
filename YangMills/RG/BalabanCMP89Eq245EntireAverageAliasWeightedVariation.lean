/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAverageAmplitudeVariation
import YangMills.RG.BalabanCMP89Eq245EntireAverageAliasStripBound
import YangMills.RG.BalabanCMP89Eq248ComplexAliasDenominator

/-!
# Alias-weighted vertical variation of the CMP89 averaging pair

Cold compiler evidence: exact source checkpoint
`4f9b86adf7428ead68c159daff0cea3ff50e2b0b`, GitHub Actions run
`31261770494` (`COLD_MODE=true`, no project-cache restore/save), warning-free
focal and audit exit zero, and four audited declarations with exactly
`[propext, Classical.choice, Quot.sound]`.

The unweighted vertical-variation estimate cannot be summed over reciprocal
aliases. This module retains one literal CMP89 (2.51) product weight while
varying the opposite-momentum pair from a complex alias momentum to its real
slice.

The half-open centered alias set is not assumed invariant under negation.
Instead, the product strip estimate is first exposed with its actual geometric
input: the normalized coordinate-zone bound. The opposite real-slice factor
is then estimated at `(-p,-m)`, with the zone transported by absolute-value
symmetry and the source weight proved even directly from its definition.

No quotient variation, noncentral alias sum variation, stabilized-denominator
lower bound, joint `B0`, contour shift or physical Green estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Product-level alias bound with the normalized coordinate zone exposed as
the real geometric premise. Membership in the half-open alias fibre is not
part of this interface. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le_of_zone
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin d → ℂ}
    (hreal : ∀ mu, (z mu).re =
      p mu + 2 * Real.pi * (m mu : ℝ))
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hzone : ∀ mu,
      |(N : ℝ)⁻¹ * (p mu + 2 * Real.pi * (m mu : ℝ))| ≤
        3 * Real.pi / 2)
    (hsmall : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageAmplitude d N z‖ ≤
      cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  rw [cmp89Eq245EntireAverageAmplitude, norm_prod,
    cmp89Eq251MultidimensionalAliasWeight]
  calc
    (∏ mu, ‖cmp89Eq245EntireAverageFactor N (z mu)‖) ≤
        ∏ mu, cmp89Eq245EntireAverageAliasStripConstant rho *
          cmp89Eq251OneDimensionalAliasWeight 1 (m mu) := by
      apply Finset.prod_le_prod
      · intro mu _
        exact norm_nonneg _
      · intro mu _
        exact norm_cmp89Eq245EntireAverageFactor_scaled_alias_le
          hN hrho (hp mu) (hreal mu) (himag mu) (hzone mu) hsmall
    _ = cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        ∏ mu, cmp89Eq251OneDimensionalAliasWeight 1 (m mu) := by
      rw [Finset.prod_mul_distrib, Fin.prod_const]

/-- The literal multidimensional reciprocal-alias weight is even. -/
theorem cmp89Eq251MultidimensionalAliasWeight_neg
    {d : ℕ} (s : ℝ) (m : Fin d → ℤ) :
    cmp89Eq251MultidimensionalAliasWeight s (-m) =
      cmp89Eq251MultidimensionalAliasWeight s m := by
  rw [cmp89Eq251MultidimensionalAliasWeight,
    cmp89Eq251MultidimensionalAliasWeight]
  apply Finset.prod_congr rfl
  intro mu _
  simp [cmp89Eq251OneDimensionalAliasWeight, abs_neg]

/-- The opposite real-slice amplitude carries the same source weight as the
original alias. The proof uses `(-p,-m)` only after exposing the coordinate
zone, so it does not assert negation stability of the half-open alias set. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_neg_realSlice_alias_le
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin d → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (hsmall : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageAmplitude d N
        (-cmp89Eq245ComplexMomentumRealSlice
          (cmp89Eq248EntireAliasMomentum z m))‖ ≤
      cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  have hzone : ∀ mu,
      |(N : ℝ)⁻¹ * (p mu + 2 * Real.pi * (m mu : ℝ))| ≤
        3 * Real.pi / 2 := by
    intro mu
    exact abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
      hN (by
        rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
        exact hm mu) (hp mu)
  have hneg :=
    norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le_of_zone
      (d := d) (N := N) hN (m := -m) (rho := rho) hrho
      (p := -p) (fun mu => by simpa using hp mu)
      (z := -cmp89Eq245ComplexMomentumRealSlice
        (cmp89Eq248EntireAliasMomentum z m))
      (fun mu => by
        simp [cmp89Eq245ComplexMomentumRealSlice,
          cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift, hreal mu]
        ring)
      (fun mu => by
        simp [cmp89Eq245ComplexMomentumRealSlice, hrho])
      (fun mu => by
        have heq :
            (N : ℝ)⁻¹ *
                ((-p) mu + 2 * Real.pi * ((-m) mu : ℝ)) =
              -((N : ℝ)⁻¹ *
                (p mu + 2 * Real.pi * (m mu : ℝ))) := by
          simp
          ring
        rw [heq, abs_neg]
        exact hzone mu)
      hsmall
  simpa only [cmp89Eq251MultidimensionalAliasWeight_neg] using hneg

/-- The opposite-momentum averaging pair varies vertically with one retained
CMP89 (2.51) source weight. Both product-rule contributions, the explicit
dimension factor and all strip constants remain visible. -/
theorem norm_cmp89Eq245EntireAveragePair_alias_sub_realSlice_le
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin d → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hsmall : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAveragePair d N
          (cmp89Eq248EntireAliasMomentum z m) -
        cmp89Eq245EntireAveragePair d N
          (cmp89Eq245ComplexMomentumRealSlice
            (cmp89Eq248EntireAliasMomentum z m))‖ ≤
      2 * ((d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d) *
        cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  let aliasZ : Fin d → ℂ := cmp89Eq248EntireAliasMomentum z m
  let aliasZ0 : Fin d → ℂ := cmp89Eq245ComplexMomentumRealSlice aliasZ
  let A := cmp89Eq245EntireAverageAmplitude d N aliasZ
  let B := cmp89Eq245EntireAverageAmplitude d N (-aliasZ)
  let A0 := cmp89Eq245EntireAverageAmplitude d N aliasZ0
  let B0 := cmp89Eq245EntireAverageAmplitude d N (-aliasZ0)
  let V : ℝ := (d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d
  let W : ℝ := cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
    cmp89Eq251MultidimensionalAliasWeight 1 m
  have haliasReal : ∀ mu, (aliasZ mu).re =
      p mu + 2 * Real.pi * (m mu : ℝ) := by
    intro mu
    simp [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift, hreal mu]
  have haliasImag : ∀ mu, |(aliasZ mu).im| ≤ rho := by
    intro mu
    simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
      cmp89Eq245AliasShift] using himag mu
  have hAvar : ‖A - A0‖ ≤ V := by
    exact norm_cmp89Eq245EntireAverageAmplitude_sub_realSlice_le
      hN hrho haliasImag
  have hBvar : ‖B - B0‖ ≤ V := by
    have hnegImag : ∀ mu, |((-aliasZ) mu).im| ≤ rho := by
      intro mu
      simpa using haliasImag mu
    simpa [B, B0, aliasZ0, V,
      cmp89Eq245ComplexMomentumRealSlice_neg] using
      (norm_cmp89Eq245EntireAverageAmplitude_sub_realSlice_le
        (d := d) (N := N) hN hrho hnegImag)
  have hAweight : ‖A‖ ≤ W := by
    exact norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le
      hN hm hrho hp haliasReal haliasImag hsmall
  have hB0weight : ‖B0‖ ≤ W := by
    simpa [B0, aliasZ0, aliasZ, W] using
      (norm_cmp89Eq245EntireAverageAmplitude_neg_realSlice_alias_le
        (d := d) (N := N) hN hm hrho hp hreal hsmall)
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (pow_nonneg (by
      rw [cmp89Eq245EntireAverageAliasStripConstant]
      positivity) d)
      (cmp89Eq251MultidimensionalAliasWeight_nonneg 1 m)
  have hrewrite : A * B - A0 * B0 =
      (A - A0) * B0 + A * (B - B0) := by ring
  change ‖A * B - A0 * B0‖ ≤ _
  rw [hrewrite]
  calc
    ‖(A - A0) * B0 + A * (B - B0)‖ ≤
        ‖(A - A0) * B0‖ + ‖A * (B - B0)‖ := norm_add_le _ _
    _ = ‖A - A0‖ * ‖B0‖ + ‖A‖ * ‖B - B0‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ V * W + W * V := by
      exact add_le_add
        (mul_le_mul hAvar hB0weight (norm_nonneg _) hV)
        (mul_le_mul hAweight hBvar (norm_nonneg _) hW)
    _ = 2 * ((d : ℝ) * (rho * Real.exp rho) * (Real.exp rho) ^ d) *
        cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
      dsimp [V, W]
      ring

end

end YangMills.RG
