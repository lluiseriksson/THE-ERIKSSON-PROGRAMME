/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointPeriodicity
import YangMills.RG.BalabanCMP89Eq251StabilizedBoundarySeam

/-!
# PRE-VALIDATION: Brillouin-face seam for each stabilized CMP89 endpoint

The source in this module is present, but its `.olean` has not yet been
materialized and its result has not yet been verified by the Lean compiler.

The sealed boundary-face producer constructs the full non-singular domain of
the displayed rational formula.  The sealed endpoint periodicity theorem
then transfers that physical period to one stabilized endpoint.  This module
composes those two facts; no global stabilized periodicity is assumed.

Contour displacement, compact-product integrability, `B0`, the owner
dictionary and window-15 attainment remain separate.
-/

namespace YangMills.RG

noncomputable section

/-- The two vertical Brillouin faces agree for one constructed stabilized
endpoint.  All displayed-domain non-singularity is produced at the lower
face before the endpoint period is used. -/
theorem cmp89Eq251ComplexStabilizedEndpointIntegrand_boundarySeam
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu mu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) := by
  rcases cmp89Eq251DisplayedDomain_of_boundaryFace
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass nu hp hface
        hreal himag with
    ⟨hunit, hreduced, hfine⟩
  exact
    cmp89Eq251ComplexStabilizedEndpointIntegrand_physicalPeriodShift_of_nonzero
      nu mu holderU endpointU hunit hreduced hfine

end

end YangMills.RG
