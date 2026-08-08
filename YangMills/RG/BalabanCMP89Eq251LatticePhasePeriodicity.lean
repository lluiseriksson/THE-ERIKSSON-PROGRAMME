/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251SignedContourPhase

/-!
# Lattice phase periodicity below CMP89 (2.49)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The physical endpoints in CMP89 lie on the unit lattice.  Their displacement
therefore has integer coordinates, even though the analytic phase API is
written in real coordinates.  This module records that dictionary explicitly
and proves the exact invariance of an endpoint phase when one alias momentum
wraps by `2*pi*N` in one coordinate.

The integer-displacement input is porting data from the source geometry, not
a periodicity hypothesis.  Periodicity is derived internally from the exact
phase formula and `exp(n * 2*pi*I) = 1`.

This does not yet reindex the centered finite alias fibre, prove periodicity
of the complete stabilized integrand, shift an integral, construct `B0`, or
attain window 15.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Real-coordinate displacement obtained from a literal displacement on the
unit lattice. -/
def cmp89Eq251LatticeDisplacement {d : ℕ}
    (u : Fin d → ℤ) : Fin d → ℝ :=
  fun mu => u mu

/-- Add one full `N`-alias period to a single complex momentum coordinate. -/
def cmp89Eq251CoordinateAliasPeriodShift {d : ℕ}
    (N : ℕ) (mu : Fin d) (z : Fin d → ℂ) : Fin d → ℂ :=
  z + Pi.single mu (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ))

/-- A coordinate alias wrap changes the entire phase by the explicit integer
multiple `2*pi*N*u_mu`. -/
theorem cmp89Eq251EntirePhase_coordinateAliasPeriodShift
    {d : ℕ} (N : ℕ) (mu : Fin d) (z : Fin d → ℂ)
    (u : Fin d → ℤ) :
    cmp89Eq251EntirePhase
        (cmp89Eq251CoordinateAliasPeriodShift N mu z)
        (cmp89Eq251LatticeDisplacement u) =
      cmp89Eq251EntirePhase z (cmp89Eq251LatticeDisplacement u) +
        (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ) * (u mu : ℂ)) := by
  simp [cmp89Eq251EntirePhase, cmp89Eq251CoordinateAliasPeriodShift,
    cmp89Eq251LatticeDisplacement, add_mul, Finset.sum_add_distrib,
    Pi.single_apply]

/-- Endpoint Fourier phases are exactly invariant under an alias wrap for a
unit-lattice displacement.  No periodicity family is accepted as input. -/
theorem exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift
    {d : ℕ} (N : ℕ) (mu : Fin d) (z : Fin d → ℂ)
    (u : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq251CoordinateAliasPeriodShift N mu z)
        (cmp89Eq251LatticeDisplacement u)) =
      Complex.exp (Complex.I *
        cmp89Eq251EntirePhase z (cmp89Eq251LatticeDisplacement u)) := by
  rw [cmp89Eq251EntirePhase_coordinateAliasPeriodShift, mul_add,
    Complex.exp_add]
  have hcycle :
      Complex.exp
          (Complex.I *
            (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ) * (u mu : ℂ))) = 1 := by
    rw [show
      Complex.I * (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ) * (u mu : ℂ)) =
        (((N : ℤ) * u mu : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I ((N : ℤ) * u mu)
  rw [hcycle, mul_one]

end

end YangMills.RG
