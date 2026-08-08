/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq250CentralLaplacianComparison

/-!
# PRE-VALIDATION: central alias lower bound in CMP89 (2.50)

The primary source is present, but this module's `.olean` has not yet been
materialized and its declarations have not yet been compiler-verified.

This module combines the two independently sealed factors in the central
alias of CMP89 (2.50): the complex averaging-amplitude lower bound from
(2.45) and the reciprocal Laplacian comparison below (2.50).  It retains the
positive source coefficient `a` as a visible parameter and also proves the
exact dictionary between the factorized core and the literal order of
multiplication and division printed in the source.

It does not sum the noncentral aliases, establish (2.51), construct the
uniform analytic strip, or identify the resulting Fourier kernel with the
canonical regional Green.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The factorized central-alias contribution in CMP89 (2.50). -/
def cmp89Eq250CentralAliasCore
    (d : ℕ) (xi mass a : ℝ) (p : Fin d → ℝ) : ℝ :=
  a * ‖cmp89Eq245ComplexAverageAmplitude d xi p‖ ^ 2 *
    (cmp89Eq249UnitLaplacianSymbol d mass p /
      cmp89Eq245ScaledLaplacianSymbol d xi mass p)

/-- The same central contribution in the literal source order
`a |u(p)|^2 / Delta^xi(p) * Delta^1(p)`. -/
def cmp89Eq250LiteralCentralAliasContribution
    (d : ℕ) (xi mass a : ℝ) (p : Fin d → ℝ) : ℝ :=
  a * ‖cmp89Eq245ComplexAverageAmplitude d xi p‖ ^ 2 /
      cmp89Eq245ScaledLaplacianSymbol d xi mass p *
    cmp89Eq249UnitLaplacianSymbol d mass p

/-- Exact algebraic dictionary from the literal source order to the
factorized central alias. -/
theorem cmp89Eq250LiteralCentralAliasContribution_eq_core
    (d : ℕ) (xi mass a : ℝ) (p : Fin d → ℝ) :
    cmp89Eq250LiteralCentralAliasContribution d xi mass a p =
      cmp89Eq250CentralAliasCore d xi mass a p := by
  simp only [cmp89Eq250LiteralCentralAliasContribution,
    cmp89Eq250CentralAliasCore, div_eq_mul_inv]
  ring

/-- Explicit lower constant obtained by multiplying the two sealed factors. -/
def cmp89Eq250CentralAliasLowerConstant (d : ℕ) (a : ℝ) : ℝ :=
  a * ((2 / Real.pi) ^ d) ^ 2 * ((Real.pi / 2) ^ 2)⁻¹

/-- The central alias of (2.50) has a scale-uniform positive lower majorant.
The positivity of `a` is kept separate from the analytic estimates. -/
theorem cmp89Eq250CentralAliasLowerConstant_le_core_inverseScale
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hmass : 0 < mass)
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq250CentralAliasLowerConstant d a ≤
      cmp89Eq250CentralAliasCore d (((L : ℝ) ^ j)⁻¹) mass a p := by
  have hxi : 0 < ((L : ℝ) ^ j)⁻¹ :=
    (cmp89Eq245_inverseScale_mem_Ioc L j).1
  have hu :=
    pow_two_div_pi_le_norm_cmp89Eq245ComplexAverageAmplitude_inverseScale
      (d := d) (L := L) (j := j) hp
  have hu0 : 0 ≤ (2 / Real.pi) ^ d :=
    (pow_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) d)
  have hu2 :
      ((2 / Real.pi) ^ d) ^ 2 ≤
        ‖cmp89Eq245ComplexAverageAmplitude d (((L : ℝ) ^ j)⁻¹) p‖ ^ 2 :=
    (sq_le_sq₀ hu0 (norm_nonneg _)).2 hu
  have hdelta := inv_pi_div_two_sq_le_cmp89Eq249_unit_div_scaled
    (d := d) (xi := ((L : ℝ) ^ j)⁻¹) (mass := mass) (p := p)
    hxi hmass hp
  have hdelta0 : 0 ≤ ((Real.pi / 2) ^ 2)⁻¹ :=
    (inv_nonneg.mpr (sq_nonneg _))
  rw [cmp89Eq250CentralAliasLowerConstant, cmp89Eq250CentralAliasCore]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hu2 hdelta hdelta0 (sq_nonneg _)) ha

/-- Literal-source-order form of the central alias lower bound. -/
theorem cmp89Eq250CentralAliasLowerConstant_le_literal_inverseScale
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hmass : 0 < mass)
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq250CentralAliasLowerConstant d a ≤
      cmp89Eq250LiteralCentralAliasContribution
        d (((L : ℝ) ^ j)⁻¹) mass a p := by
  rw [cmp89Eq250LiteralCentralAliasContribution_eq_core]
  exact cmp89Eq250CentralAliasLowerConstant_le_core_inverseScale ha hmass hp

/-- The explicit central lower constant is strictly positive when the source
coefficient is. -/
theorem cmp89Eq250CentralAliasLowerConstant_pos
    {d : ℕ} {a : ℝ} (ha : 0 < a) :
    0 < cmp89Eq250CentralAliasLowerConstant d a := by
  rw [cmp89Eq250CentralAliasLowerConstant]
  exact mul_pos
    (mul_pos ha (pow_pos (pow_pos (div_pos (by norm_num) Real.pi_pos) d) 2))
    (inv_pos.mpr (pow_pos Real.pi_div_two_pos 2))

end

end YangMills.RG
