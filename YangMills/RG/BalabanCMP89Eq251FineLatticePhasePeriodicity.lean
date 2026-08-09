/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249FinePhaseScaleNoGo
import YangMills.RG.BalabanCMP89Eq251LatticePhasePeriodicity

/-!
# PRE-VALIDATION: physical fine-lattice endpoint phase periodicity

Source is present at the checkpoint containing this file; its `.olean` has not
yet been materialized and the result is not yet compiler-verified.

CMP89 (2.43)--(2.49) uses physical sites in `xi Z^d`, with
`xi = (L^j)^(-1)`, while a centered-alias wrap changes the already-aliased
momentum by `2*pi*L^j`.  Their product is the literal integer phase
`2*pi*u`.  This module proves that cancellation explicitly.

This is a seam input, not the invalid common-phase factorization refuted by
`cmp89Eq249_halfScale_singleAliasPhase_ne_one`: individual `2*pi` aliases
remain nontrivial at fine physical displacements.  No displayed-integrand
periodicity, contour shift, physical `B0`, window-15 attainment, terminal
field or `TermSource` is claimed here.
-/

namespace YangMills.RG

noncomputable section

/-- A full centered-alias wrap changes a phase with an arbitrary real
displacement by the literal coordinate contribution. -/
theorem cmp89Eq251EntirePhase_coordinateAliasPeriodShift_real
    {d : ℕ} (N : ℕ) (mu : Fin d) (z : Fin d → ℂ)
    (u : Fin d → ℝ) :
    cmp89Eq251EntirePhase
        (cmp89Eq251CoordinateAliasPeriodShift N mu z) u =
      cmp89Eq251EntirePhase z u +
        (((2 * Real.pi * (N : ℝ) : ℝ) : ℂ) * (u mu : ℂ)) := by
  simp [cmp89Eq251EntirePhase, cmp89Eq251CoordinateAliasPeriodShift,
    add_mul, Finset.sum_add_distrib, Pi.single_apply]

/-- At physical fine-lattice spacing `1/N`, the alias-wrap increment is
exactly the integer phase `2*pi*u_mu`. -/
theorem cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine
    {d : ℕ} (N : ℕ) [NeZero N] (mu : Fin d) (z : Fin d → ℂ)
    (u : Fin d → ℤ) :
    cmp89Eq251EntirePhase
        (cmp89Eq251CoordinateAliasPeriodShift N mu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) u) =
      cmp89Eq251EntirePhase z
          (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) u) +
        (((2 * Real.pi : ℝ) : ℂ) * (u mu : ℂ)) := by
  rw [cmp89Eq251EntirePhase_coordinateAliasPeriodShift_real]
  congr 1
  unfold cmp89Eq249PhysicalFineLatticeDisplacement
  have hN : (N : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  push_cast
  field_simp [hN]
  ring_nf

/-- Endpoint Fourier phases on `N^(-1) Z^d` are invariant under the physical
alias-cycle wrap `2*pi*N`.  The proof derives periodicity from the fine-site
integer `u`; it accepts no periodicity family as input. -/
theorem exp_I_cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine
    {d : ℕ} (N : ℕ) [NeZero N] (mu : Fin d) (z : Fin d → ℂ)
    (u : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq251CoordinateAliasPeriodShift N mu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) u)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase z
        (cmp89Eq249PhysicalFineLatticeDisplacement ((N : ℝ)⁻¹) u)) := by
  rw [cmp89Eq251EntirePhase_coordinateAliasPeriodShift_physicalFine,
    mul_add, Complex.exp_add]
  have hcycle :
      Complex.exp
          (Complex.I * (((2 * Real.pi : ℝ) : ℂ) * (u mu : ℂ))) = 1 := by
    rw [show
      Complex.I * (((2 * Real.pi : ℝ) : ℂ) * (u mu : ℂ)) =
        (u mu : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring_nf]
    exact Complex.exp_int_mul_two_pi_mul_I (u mu)
  rw [hcycle, mul_one]

end

end YangMills.RG
