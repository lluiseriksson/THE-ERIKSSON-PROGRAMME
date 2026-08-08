/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251AliasAmplitudeUpper

/-!
# PRE-VALIDATION: printed-alias denominator nonvanishing below CMP89 (2.51)

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

This leaf isolates the single physical fact needed by the entire averaging
dictionary: the expanded-zone sinc lower bound keeps the removable
exponential slope away from zero at every printed alias.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The denominator slope of CMP89 (2.45) is nonzero at every printed alias. -/
theorem cmp89Eq245RemovableExpSlope_scaled_alias_ne_zero
    {N : ℕ} (hN : 0 < N) {m : ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasIntegers N)
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    cmp89Eq245RemovableExpSlope
        ((N : ℝ)⁻¹ * (p + 2 * Real.pi * (m : ℝ))) ≠ 0 := by
  have hsinc := one_div_three_pi_le_abs_sinc_scaled_alias
    (N := N) (m := m) (p := p) hN hm hp
  have hsincPos :
      0 < |Real.sinc (((N : ℝ)⁻¹ *
        (p + 2 * Real.pi * (m : ℝ))) / 2)| := by
    exact (div_pos (by norm_num) (mul_pos (by norm_num) Real.pi_pos)).trans_le
      hsinc
  intro hzero
  have hzeroNorm :
      |Real.sinc (((N : ℝ)⁻¹ *
        (p + 2 * Real.pi * (m : ℝ))) / 2)| = 0 := by
    rw [← norm_cmp89Eq245RemovableExpSlope, hzero, norm_zero]
  exact (ne_of_gt hsincPos) hzeroNorm

end

end YangMills.RG
