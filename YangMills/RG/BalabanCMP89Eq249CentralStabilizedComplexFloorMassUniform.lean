/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloor
import YangMills.RG.BalabanCMP89Eq249NoncentralRealGap

/-!
# Mass-uniform complex floor for the stabilized CMP89 (2.49) denominator

Compiler-verified at exact source checkpoint
`733ecbb60d43b72e04f9740eb825251b397503b8` by cold GitHub Actions run
`31880056149`.  Restoration and saving of `.lake/build` were skipped.  The
focal completed 8,441 jobs, and all three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The sealed vertical-variation estimate already assumes the explicit source
mass window `mass ^ 2 ≤ 1`.  Its existing complex-floor consumer additionally
asked for `0 < mass` only to obtain the real-slice floor.  The mass-uniform
real theorem now supplies that floor directly, so this module removes exactly
the obsolete positivity premise while preserving every scalar radius,
amplitude and complex-window obligation.

This is not a proof that the RG flow satisfies the mass window or the complex
window, and it does not construct a regional `B0`, attain window 15, discharge
a terminal field, or inhabit `TermSource`.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

theorem sub_variation_le_norm_cmp89Eq249CentralStabilizedAliasDenominator_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
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
    exact cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform ha hp
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

theorem cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
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
    sub_variation_le_norm_cmp89Eq249CentralStabilizedAliasDenominator_massUniform
      (L := L) (j := j) (mass := mass) ha hrho hradius hmass
      hp hreal himag hamplitude
  have hpos :
      0 < cmp89Eq249CentralStabilizedLowerConstant 4 a -
        cmp89Eq249CentralStabilizedDenominatorVariationBound a rho := by
    simpa [CMP89Eq249CentralStabilizedComplexWindow] using hwindow
  exact norm_pos_iff.mp (hpos.trans_le hlower)

theorem norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
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
      (sub_variation_le_norm_cmp89Eq249CentralStabilizedAliasDenominator_massUniform
        (L := L) (j := j) (mass := mass) ha hrho hradius hmass
        hp hreal himag hamplitude)
  have hlowerPos : 0 < lower := by
    simpa [lower, CMP89Eq249CentralStabilizedComplexWindow] using hwindow
  have hdenPos : 0 < ‖den‖ := hlowerPos.trans_le hlower
  change ‖den⁻¹‖ ≤ _
  rw [norm_inv, cmp89Eq249CentralStabilizedComplexReciprocalBound]
  exact (inv_le_inv₀ hdenPos hlowerPos).2 hlower

end

end YangMills.RG
