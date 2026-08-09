/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexEndpointAmplitudeFactorization
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointCentralFineUpper

/-!
# PRE-VALIDATION: phase-free endpoint-amplitude bound below CMP89 (2.49)

Source is present, its `.olean` has not yet been materialized, and the results
have not yet been verified by the compiler.

The exact endpoint factorization is already cold-sealed.  This file bounds its
phase-free bracket: the zero-alias branch uses the literal scaled-difference
and averaging-amplitude strip bounds, while the noncentral branch multiplies
the central fine-symbol bound by the already sealed norm of the complete
noncentral quotient sum.

No endpoint phase is bounded here.  In particular, this file does not absorb
the separate one-link factor `exp rho`, construct the physical owner bound or
the complete `B0`, attain window 15 or discharge a terminal field.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit scale-uniform majorant for the phase-free central endpoint
amplitude. -/
def cmp89Eq251ComplexCentralEndpointAmplitudeBound (rho : ℝ) : ℝ :=
  (Real.pi + rho * Real.exp rho) * Real.exp rho ^ 4

/-- The phase-free zero-alias endpoint branch is bounded uniformly in the
alias scale. -/
theorem norm_cmp89Eq251ComplexCentralEndpointAmplitude_le_bound
    {L j : ℕ} [NeZero L] {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (mu : Fin 4) :
    ‖cmp89Eq251ComplexCentralEndpointAmplitude L j z mu‖ ≤
      cmp89Eq251ComplexCentralEndpointAmplitudeBound rho := by
  obtain ⟨hxi, hxi1⟩ := cmp89Eq245_inverseScale_mem_Ioc L j
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hpMu : |(z mu).re| ≤ Real.pi := by
    rw [hreal mu]
    exact hp mu
  have hdiff :
      ‖cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹) (-z mu)‖ ≤
        Real.pi + rho * Real.exp rho := by
    have hraw :=
      norm_cmp89Eq245EntireScaledDifference_le_abs_re_add_vertical
        hxi hxi1 hrho (by simpa using himag mu : |(-z mu).im| ≤ rho)
    calc
      ‖cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹) (-z mu)‖ ≤
          |(-z mu).re| + rho * Real.exp rho := hraw
      _ = |(z mu).re| + rho * Real.exp rho := by simp
      _ ≤ Real.pi + rho * Real.exp rho :=
        add_le_add hpMu (le_refl _)
  have havg :
      ‖cmp89Eq245EntireAverageAmplitude 4 (L ^ j) z‖ ≤
        Real.exp rho ^ 4 :=
    norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow hN hrho himag
  rw [cmp89Eq251ComplexCentralEndpointAmplitude,
    cmp89Eq251ComplexCentralEndpointAmplitudeBound, norm_mul]
  exact mul_le_mul hdiff havg (norm_nonneg _)
    (add_nonneg Real.pi_pos.le (mul_nonneg hrho (Real.exp_pos rho).le))

/-- Explicit scale-uniform majorant for the complete phase-free endpoint
amplitude.  Its two summands retain the central/noncentral split. -/
def cmp89Eq251ComplexEndpointAmplitudeBound (rho : ℝ) : ℝ :=
  cmp89Eq251ComplexCentralEndpointAmplitudeBound rho +
    cmp89Eq251CentralFineSymbolStripUpperBound rho *
      cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho

/-- The complete phase-free endpoint bracket is bounded without replacing the
sealed norm of the noncentral quotient sum by a sum of norms. -/
theorem norm_cmp89Eq251ComplexEndpointAmplitude_le_bound
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq251ComplexEndpointAmplitude L j mass z mu‖ ≤
      cmp89Eq251ComplexEndpointAmplitudeBound rho := by
  have hcentral :=
    norm_cmp89Eq251ComplexCentralEndpointAmplitude_le_bound
      (L := L) (j := j) hrho hp hreal himag mu
  have hfine :=
    norm_cmp89Eq249CentralEntireFineSymbol_le_stripUpperBound
      (L := L) (j := j) hmass hrho hp hreal himag
  have hsum :=
    norm_cmp89Eq251ComplexNoncentralEndpointQuotientSum_le_bound
      (L := L) (j := j) (mass := mass) hrho hradius hp hreal himag
        hamplitude mu
  have hfineBoundNonneg :
      0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
    rw [cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hnoncentral :
      ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq251ComplexNoncentralEndpointQuotientSum L j mass z mu‖ ≤
        cmp89Eq251CentralFineSymbolStripUpperBound rho *
          cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho := by
    rw [norm_mul]
    exact mul_le_mul hfine hsum (norm_nonneg _) hfineBoundNonneg
  rw [cmp89Eq251ComplexEndpointAmplitude,
    cmp89Eq251ComplexEndpointAmplitudeBound]
  exact (norm_add_le _ _).trans (add_le_add hcentral hnoncentral)

end

end YangMills.RG
