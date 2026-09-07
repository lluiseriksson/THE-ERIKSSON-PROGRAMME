/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251FineLatticeStabilizedEndpointPeriodicity
import YangMills.RG.BalabanCMP89Eq251StabilizedBoundarySeam

/-!
# Cold-sealed fine-lattice stabilized endpoint boundary seam

Compiler-verified at exact source checkpoint
`72915aefdfcf886a0fc6afef915967bc34ad398e` by cold GitHub Actions run
`31338609395`. Restoration and saving of `.lake/build` were skipped. The focal
and audit exited zero; the audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`.

The nonvanishing input is the sealed full-polydisc producer: every coordinate
of `z` may already be complex, subject only to `|Im z_k| <= rho`.  This is the
domain required by the intermediate stages of the four-coordinate contour
shift.  The endpoint displacement is the physical fine-lattice value
`u/(L^j)` and `alpha` is literally zero.

This module proves only equality of the two vertical Brillouin faces.  The
one-coordinate shift, product integrability, four-coordinate telescope,
normalized integration, physical `B0`, window-15 attainment and terminal
fields remain open.
-/

namespace YangMills.RG

noncomputable section

/-- The two vertical Brillouin faces agree for one stabilized endpoint at
physical fine-lattice displacement `u/(L^j)`.  Non-singularity is constructed
on the complete polydisc, not on a one-coordinate slice. -/
theorem cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFine_boundarySeam
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu mu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (holderDisplacement : Fin 4 → ℝ) (endpointU : Fin 4 → ℤ) :
    cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) =
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0 z mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU) := by
  rcases cmp89Eq251DisplayedDomain_of_boundaryFace
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass nu hp hface
        hreal himag with
    ⟨hunit, hreduced, hfine⟩
  exact
    cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_physicalFinePeriodShift_of_nonzero
      nu mu holderDisplacement endpointU hunit hreduced hfine

end

end YangMills.RG
