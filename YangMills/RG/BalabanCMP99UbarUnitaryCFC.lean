/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogUnitaryCFC
import YangMills.RG.BalabanCMP99UbarUnitaryCovariance

/-!
# Canonical CMP99 unitary blocks from near-identity unitary data

The earlier unitary layer accepted skew-adjointness of each Mercator
coordinate as an explicit certificate.  The CFC closure now produces that
certificate from the physical hypotheses themselves: the deviations are
unitary and lie in the open Mercator ball.

This file therefore exposes the canonical unitary factor and block with no
`hlog` argument.  It deliberately stops at `unitary A`; a special-unitary
codomain additionally requires a source-valid no-winding/tracelessness input.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [IsScalarTower ℝ ℂ A]
  [NormedAlgebra ℚ A]

/-- The physical CMP99 exponent for a finite family of unitary deviations. -/
noncomputable def cmp99UbarUnitaryExponent {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → unitary A) : A :=
  cmp99UbarExponent s w fun i => (D i : A)

/-- The physical unitary hypotheses automatically make the complete CMP99
exponent skew-adjoint. -/
theorem cmp99UbarUnitaryExponent_mem_skewAdjoint {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (D : ι → unitary A)
    (hD : ∀ i ∈ s, ‖(D i : A) - 1‖ < 1) :
    cmp99UbarUnitaryExponent s w D ∈ skewAdjoint A := by
  exact cmp99UbarExponent_mem_skewAdjoint s w (fun i => (D i : A))
    fun i hi => nearLog_unitary_sub_one_mem_skewAdjoint (D i) (hD i hi)

/-- The canonical CMP99 exponential factor obtained directly from
near-identity unitary data, without an externally supplied logarithm
certificate. -/
noncomputable def cmp99UbarUnitaryFactorOfNearIdentity {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → unitary A)
    (hD : ∀ i ∈ s, ‖(D i : A) - 1‖ < 1) : unitary A :=
  cmp99UbarUnitaryFactor s w (fun i => (D i : A))
    fun i hi => nearLog_unitary_sub_one_mem_skewAdjoint (D i) (hD i hi)

@[simp] theorem cmp99UbarUnitaryFactorOfNearIdentity_coe {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → unitary A)
    (hD : ∀ i ∈ s, ‖(D i : A) - 1‖ < 1) :
    (cmp99UbarUnitaryFactorOfNearIdentity s w D hD : A) =
      NormedSpace.exp (cmp99UbarUnitaryExponent s w D) :=
  rfl

/-- The full canonical CMP99 unitary block from the physical unitary
deviations and a coarse unitary. -/
noncomputable def cmp99UbarUnitaryBlockOfNearIdentity {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → unitary A)
    (hD : ∀ i ∈ s, ‖(D i : A) - 1‖ < 1)
    (coarse : unitary A) : unitary A :=
  cmp99UbarUnitaryFactorOfNearIdentity s w D hD * coarse

@[simp] theorem cmp99UbarUnitaryBlockOfNearIdentity_coe {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → unitary A)
    (hD : ∀ i ∈ s, ‖(D i : A) - 1‖ < 1)
    (coarse : unitary A) :
    (cmp99UbarUnitaryBlockOfNearIdentity s w D hD coarse : A) =
      NormedSpace.exp (cmp99UbarUnitaryExponent s w D) * (coarse : A) :=
  rfl

end

end YangMills.RG
