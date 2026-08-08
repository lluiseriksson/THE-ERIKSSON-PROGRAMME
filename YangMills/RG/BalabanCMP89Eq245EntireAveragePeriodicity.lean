/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248EntireFourierSymbols
import YangMills.RG.BalabanCMP89Eq251LatticePhasePeriodicity

/-!
# Alias-period invariance of the entire averaging amplitude

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and this result has not yet been verified by the compiler.

The finite geometric continuation of the averaging quotient has fundamental
period `2*pi*N` in each momentum coordinate.  This module derives that period
from the literal exponential formula, first for an arbitrary integer multiple
in one coordinate and then for the full amplitude and its holomorphic
opposite-momentum pairing.

The period here is the fine-lattice alias period `2*pi*N`.  It is not the
unit-lattice period `2*pi`, and no periodicity of the complete alias
denominator or of the stabilized CMP89 integrand is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The exponential base of the finite average is invariant under every
integer multiple of its exact `2*pi*N` period. -/
theorem cmp89Eq245EntireAverageBase_add_int_aliasPeriod
    {N : ℕ} (hN : 0 < N) (k : ℤ) (z : ℂ) :
    cmp89Eq245EntireAverageBase N
        (z + (k : ℂ) * (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ))) =
      cmp89Eq245EntireAverageBase N z := by
  have hNcomplex : (N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  unfold cmp89Eq245EntireAverageBase
  have harg :
      Complex.I *
          (-((N : ℂ)⁻¹ *
            (z + (k : ℂ) * (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ))))) =
        Complex.I * (-((N : ℂ)⁻¹ * z)) +
          ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp [hNcomplex]
    ring
  rw [harg, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- The pole-free one-coordinate averaging factor has exact integer alias
periods. -/
theorem cmp89Eq245EntireAverageFactor_add_int_aliasPeriod
    {N : ℕ} (hN : 0 < N) (k : ℤ) (z : ℂ) :
    cmp89Eq245EntireAverageFactor N
        (z + (k : ℂ) * (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ))) =
      cmp89Eq245EntireAverageFactor N z := by
  unfold cmp89Eq245EntireAverageFactor
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [cmp89Eq245EntireAverageBase_add_int_aliasPeriod hN k z]

/-- A positive coordinate alias wrap preserves the complete averaging
amplitude. -/
theorem cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq245EntireAverageAmplitude d N
        (cmp89Eq251CoordinateAliasPeriodShift N mu z) =
      cmp89Eq245EntireAverageAmplitude d N z := by
  unfold cmp89Eq245EntireAverageAmplitude
  apply Finset.prod_congr rfl
  intro nu _
  by_cases hmu : nu = mu
  · subst nu
    simpa [cmp89Eq251CoordinateAliasPeriodShift] using
      (cmp89Eq245EntireAverageFactor_add_int_aliasPeriod
        hN (1 : ℤ) (z mu))
  · simp [cmp89Eq251CoordinateAliasPeriodShift, Pi.single_apply, hmu]

/-- The opposite-momentum amplitude is preserved by the corresponding
negative alias wrap. -/
theorem cmp89Eq245EntireAverageAmplitude_neg_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq245EntireAverageAmplitude d N
        (-(cmp89Eq251CoordinateAliasPeriodShift N mu z)) =
      cmp89Eq245EntireAverageAmplitude d N (-z) := by
  unfold cmp89Eq245EntireAverageAmplitude
  apply Finset.prod_congr rfl
  intro nu _
  by_cases hmu : nu = mu
  · subst nu
    simpa [cmp89Eq251CoordinateAliasPeriodShift] using
      (cmp89Eq245EntireAverageFactor_add_int_aliasPeriod
        hN (-1 : ℤ) (-z mu))
  · simp [cmp89Eq251CoordinateAliasPeriodShift, Pi.single_apply, hmu]

/-- The holomorphic averaging pairing is invariant under one coordinate
alias wrap. -/
theorem cmp89Eq245EntireAveragePair_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq245EntireAveragePair d N
        (cmp89Eq251CoordinateAliasPeriodShift N mu z) =
      cmp89Eq245EntireAveragePair d N z := by
  rw [cmp89Eq245EntireAveragePair, cmp89Eq245EntireAveragePair,
    cmp89Eq245EntireAverageAmplitude_coordinateAliasPeriodShift hN,
    cmp89Eq245EntireAverageAmplitude_neg_coordinateAliasPeriodShift hN]

end

end YangMills.RG
