/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedDenominatorVariation
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedRealLower

/-!
# Complex floor for the stabilized CMP89 (2.49) denominator

Cold compiler evidence: source checkpoint
`4f62edc183ceac0fde4b7b2b847f2270f458545b`, GitHub Actions run
`31266722921` (`COLD_MODE=true`, no project-cache restore/save), focal and
audit exit zero, and all three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The real-slice floor and the sealed vertical-variation budget combine by the
reverse triangle inequality.  This module keeps their comparison as one
literal scalar window.  When that window holds, the stabilized denominator is
nonzero throughout the strip and its reciprocal has an explicit uniform
bound.

This is a reduction to a scalar target, not a proof that the source flow
attains it.  No contour shift, Fourier/physical rate dictionary, regional
Green estimate or window-15 contraction is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal joint scalar window comparing the real floor with the full
vertical variation of the same stabilized denominator. -/
def CMP89Eq249CentralStabilizedComplexWindow (a rho : ℝ) : Prop :=
  cmp89Eq249CentralStabilizedDenominatorVariationBound a rho <
    cmp89Eq249CentralStabilizedLowerConstant 4 a

/-- Explicit reciprocal bound left after subtracting the complete vertical
variation from the real floor. -/
def cmp89Eq249CentralStabilizedComplexReciprocalBound
    (a rho : ℝ) : ℝ :=
  (cmp89Eq249CentralStabilizedLowerConstant 4 a -
    cmp89Eq249CentralStabilizedDenominatorVariationBound a rho)⁻¹

/-- The real floor minus the full vertical budget remains below the norm of
the complex stabilized denominator. -/
theorem sub_variation_le_norm_cmp89Eq249CentralStabilizedAliasDenominator
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    cmp89Eq249CentralStabilizedLowerConstant 4 a -
        cmp89Eq249CentralStabilizedDenominatorVariationBound a rho ≤
      ‖cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z‖ := by
  let z0 : Fin 4 → ℂ := cmp89Eq245ComplexMomentumRealSlice z
  let den := cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z
  let den0 := cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z0
  let floor := cmp89Eq249CentralStabilizedLowerConstant 4 a
  let variation := cmp89Eq249CentralStabilizedDenominatorVariationBound a rho
  have hz0 : z0 = fun mu => (p mu : ℂ) := by
    funext mu
    simp [z0, cmp89Eq245ComplexMomentumRealSlice, hreal mu]
  have hvariation : ‖den - den0‖ ≤ variation := by
    simpa [den, den0, z0, variation] using
      (norm_cmp89Eq249CentralStabilizedAliasDenominator_sub_realSlice_le
        (L := L) (j := j) (mass := mass) ha hrho hradius hmass
        hp hreal himag hamplitude)
  have hfloorRe : floor ≤ den0.re := by
    change cmp89Eq249CentralStabilizedLowerConstant 4 a ≤
      (cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z0).re
    rw [hz0]
    exact cmp89Eq249CentralStabilizedLowerConstant_le_re ha hmassPos hp
  have hfloorNorm : floor ≤ ‖den0‖ := by
    exact hfloorRe.trans
      ((le_abs_self den0.re).trans (Complex.abs_re_le_norm den0))
  have htriangle : ‖den0‖ ≤ ‖den‖ + ‖den - den0‖ := by
    calc
      ‖den0‖ = ‖den - (den - den0)‖ := by
        congr 1
        ring
      _ ≤ ‖den‖ + ‖den - den0‖ := norm_sub_le _ _
  linarith

/-- The literal scalar window makes the stabilized denominator nonzero at
every point of the common complex strip. -/
theorem cmp89Eq249CentralStabilizedAliasDenominator_ne_zero
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 := by
  have hlower :=
    sub_variation_le_norm_cmp89Eq249CentralStabilizedAliasDenominator
      (L := L) (j := j) (mass := mass) ha hmassPos hrho hradius hmass
      hp hreal himag hamplitude
  have hpos :
      0 < cmp89Eq249CentralStabilizedLowerConstant 4 a -
        cmp89Eq249CentralStabilizedDenominatorVariationBound a rho := by
    simpa [CMP89Eq249CentralStabilizedComplexWindow] using hwindow
  exact norm_pos_iff.mp (hpos.trans_le hlower)

/-- Uniform reciprocal bound produced by the same literal scalar window. -/
theorem norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖(cmp89Eq249CentralStabilizedAliasDenominator
        4 L j mass a z)⁻¹‖ ≤
      cmp89Eq249CentralStabilizedComplexReciprocalBound a rho := by
  let den := cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z
  let lower := cmp89Eq249CentralStabilizedLowerConstant 4 a -
    cmp89Eq249CentralStabilizedDenominatorVariationBound a rho
  have hlower : lower ≤ ‖den‖ := by
    simpa [lower, den] using
      (sub_variation_le_norm_cmp89Eq249CentralStabilizedAliasDenominator
        (L := L) (j := j) (mass := mass) ha hmassPos hrho hradius hmass
        hp hreal himag hamplitude)
  have hlowerPos : 0 < lower := by
    simpa [lower, CMP89Eq249CentralStabilizedComplexWindow] using hwindow
  have hdenPos : 0 < ‖den‖ := hlowerPos.trans_le hlower
  change ‖den⁻¹‖ ≤ _
  rw [norm_inv, cmp89Eq249CentralStabilizedComplexReciprocalBound]
  exact (inv_le_inv₀ hdenPos hlowerPos).2 hlower

end

end YangMills.RG
