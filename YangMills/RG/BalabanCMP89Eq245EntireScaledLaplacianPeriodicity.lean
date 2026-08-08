/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245EntireAveragePeriodicity

/-!
# Alias-period invariance of the entire fine Laplacian

Compiler verification: exact source checkpoint
`b38d7f1226fa68be399bea0f972fe3ddaf9bf040`, cold GitHub Actions run
`31282931967` (8,447 jobs; focal and three-declaration axiom audit exit zero;
restore and save of `.lake/build` both skipped).

At inverse integer spacing `xi = 1/N`, the entire difference and the
opposite-momentum Laplacian pairing have exact coordinate period `2*pi*N`.
The proof derives this from the same exponential cycle already sealed for the
finite geometric average; no abstract periodicity family is accepted.

This module does not yet form the average/Laplacian quotient, reindex the
finite alias sum, or prove the distinct `2*pi` period of the unit-lattice
symbol.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- At spacing `1/N`, the entire fine difference has every integer multiple
of the exact alias period `2*pi*N`. -/
theorem cmp89Eq245EntireScaledDifference_invNat_add_int_aliasPeriod
    {N : ℕ} (hN : 0 < N) (k : ℤ) (z : ℂ) :
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹)
        (z + (k : ℂ) * (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ))) =
      cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) z := by
  have hbase :=
    cmp89Eq245EntireAverageBase_add_int_aliasPeriod hN k z
  simpa [cmp89Eq245EntireScaledDifference,
    cmp89Eq245EntireAverageBase] using
      congrArg
        (fun w : ℂ =>
          (w - 1) / ((((N : ℝ)⁻¹ : ℝ) : ℂ))) hbase

/-- The opposite-momentum product of fine differences is invariant under one
scalar alias wrap. -/
theorem cmp89Eq245EntireScaledDifferencePair_aliasPeriod
    {N : ℕ} (hN : 0 < N) (z : ℂ) :
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹)
          (z + (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ))) *
        cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹)
          (-(z + (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ)))) =
      cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) z *
        cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) (-z) := by
  rw [show
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹)
        (z + (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ))) =
      cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) z by
        simpa using
          (cmp89Eq245EntireScaledDifference_invNat_add_int_aliasPeriod
            hN (1 : ℤ) z)]
  rw [show
    cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹)
        (-(z + (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ)))) =
      cmp89Eq245EntireScaledDifference ((N : ℝ)⁻¹) (-z) by
        simpa [add_comm] using
          (cmp89Eq245EntireScaledDifference_invNat_add_int_aliasPeriod
            hN (-1 : ℤ) (-z))]

/-- The entire fine-lattice Laplacian at spacing `1/N` is invariant under a
coordinate alias wrap. -/
theorem cmp89Eq245EntireScaledLaplacianSymbol_invNat_coordinateAliasPeriodShift
    {d N : ℕ} (hN : 0 < N) (mass : ℝ) (mu : Fin d) (z : Fin d → ℂ) :
    cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass
        (cmp89Eq251CoordinateAliasPeriodShift N mu z) =
      cmp89Eq245EntireScaledLaplacianSymbol d ((N : ℝ)⁻¹) mass z := by
  unfold cmp89Eq245EntireScaledLaplacianSymbol
  congr 1
  apply Finset.sum_congr rfl
  intro nu _
  by_cases hmu : nu = mu
  · subst nu
    simpa [cmp89Eq251CoordinateAliasPeriodShift] using
      (cmp89Eq245EntireScaledDifferencePair_aliasPeriod hN (z mu))
  · simp [cmp89Eq251CoordinateAliasPeriodShift, hmu]

end

end YangMills.RG
