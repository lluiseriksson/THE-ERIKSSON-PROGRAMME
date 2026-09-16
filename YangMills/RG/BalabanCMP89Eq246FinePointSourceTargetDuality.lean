/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246DirectedEndpointPhase

/-!
# Target/source phase duality below CMP89 (2.46)

The positive Fourier phase used to synthesize an output endpoint is exactly
the normalized fine-point-source vector evaluated at the negated endpoint.
This elementary identity is kept named because it is the endpoint-orientation
input to the direct/transpose pairing of the complete Eq. (2.46) solve.

No precision symmetry, alias reflection, finite-grid aliasing, regional
estimate, window-15 attainment, terminal field, or `TermSource` inhabitant is
assumed or asserted.
-/

namespace YangMills.RG

noncomputable section

/-- The negative-source phase at the negated endpoint is the positive target
phase at the original endpoint. -/
theorem cmp89Eq246FinePointSourceAliasVector_negEndpoint_eq_targetPhase
    {d L j : ℕ} (z : Fin d → ℂ) (m : CMP89Eq246AliasIndex d L j)
    (endpoint : Fin d → ℝ) :
    cmp89Eq246FinePointSourceAliasVector d L j z
        (fun mu => -endpoint mu) m =
      Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1) endpoint) := by
  have hphase :
      cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1) (fun mu => -endpoint mu) =
        -cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1) endpoint := by
    simp only [cmp89Eq251EntirePhase, Complex.ofReal_neg]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro mu _
    ring
  rw [cmp89Eq246FinePointSourceAliasVector, hphase]
  congr 1
  ring

/-- Integer fine-lattice endpoint form of the same target/source duality. -/
theorem cmp89Eq246FinePointSourceAliasVector_negPhysicalEndpoint_eq_targetPhase
    {d L j : ℕ} (xi : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) (endpoint : Fin d → ℤ) :
    cmp89Eq246FinePointSourceAliasVector d L j z
        (cmp89Eq249PhysicalFineLatticeDisplacement xi
          (fun mu => -endpoint mu)) m =
      Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum z m.1)
          (cmp89Eq249PhysicalFineLatticeDisplacement xi endpoint)) := by
  have hneg :
      cmp89Eq249PhysicalFineLatticeDisplacement xi (fun mu => -endpoint mu) =
        fun mu => -cmp89Eq249PhysicalFineLatticeDisplacement xi endpoint mu := by
    funext mu
    simp only [cmp89Eq249PhysicalFineLatticeDisplacement, Int.cast_neg]
    ring
  rw [hneg]
  exact cmp89Eq246FinePointSourceAliasVector_negEndpoint_eq_targetPhase
    z m (cmp89Eq249PhysicalFineLatticeDisplacement xi endpoint)

end

end YangMills.RG
