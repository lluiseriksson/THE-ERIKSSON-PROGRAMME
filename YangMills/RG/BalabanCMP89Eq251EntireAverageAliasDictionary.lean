/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251EntireAverageAmplitude
import YangMills.RG.BalabanCMP89Eq251AliasSlopeNonzero

/-!
# PRE-VALIDATION: printed-alias dictionary for the entire CMP89 amplitude

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

This module keeps the physical alias geometry on the far side of an `.olean`
boundary from the generic finite geometric identity.  The expanded-zone sinc
lower bound proves the printed denominator is nonzero, after which the entire
factor agrees exactly with CMP89 (2.45) on every real printed alias.

No analytic strip, complex denominator lower bound, contour displacement, or
regional-Green estimate is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Coordinate-specialized real-slice dictionary for a printed alias. -/
theorem cmp89Eq245EntireAverageFactor_ofReal_scaled_alias_eq
    {N : ℕ} (hN : 0 < N) {m : ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasIntegers N)
    {p : ℝ} (hp : |p| ≤ Real.pi) :
    cmp89Eq245EntireAverageFactor N
        ((p + 2 * Real.pi * (m : ℝ) : ℝ) : ℂ) =
      cmp89Eq245ComplexAverageFactor (N : ℝ)⁻¹
        (p + 2 * Real.pi * (m : ℝ)) := by
  exact cmp89Eq245EntireAverageFactor_ofReal_eq
    (N := N) (q := p + 2 * Real.pi * (m : ℝ)) hN
    (cmp89Eq245RemovableExpSlope_scaled_alias_ne_zero
      (N := N) (m := m) (p := p) hN hm hp)

/-- Exact real-slice dictionary on every alias printed in CMP89 (2.45). -/
theorem cmp89Eq245EntireAverageAmplitude_ofReal_scaled_alias_eq
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq245EntireAverageAmplitude d N
        (fun mu => ((p mu + 2 * Real.pi * (m mu : ℝ) : ℝ) : ℂ)) =
      cmp89Eq245ComplexAverageAmplitude d (N : ℝ)⁻¹
        (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) := by
  rw [cmp89Eq245EntireAverageAmplitude,
    cmp89Eq245ComplexAverageAmplitude]
  apply Finset.prod_congr rfl
  intro mu hmu
  apply cmp89Eq245EntireAverageFactor_ofReal_scaled_alias_eq
    (N := N) (m := m mu) (p := p mu) hN
  · rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
    exact hm mu
  · exact hp mu

end

end YangMills.RG
