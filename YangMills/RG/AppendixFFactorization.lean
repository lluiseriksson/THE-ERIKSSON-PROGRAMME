/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFCover
import YangMills.RG.MayerCoverFactorization

/-!
# Appendix-F target-cover factorization

This file exposes the already verified Ω-component Mayer factorization through
the finite `OmegaTargetCover` interface.  It is an adapter layer: the analytic
factorization still comes from `MayerCoverFactorization`, while the target-cover
carrier records the finite active set that future Appendix-F estimates measure.

Honest scope: no Yang--Mills activity estimate, source constant, or continuum
claim is added here.  The theorem below only repackages an existing finite
ultralocal factorization for target-cover consumers.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

namespace OmegaTargetCover

/-- Target-cover form of the Ω-component factorization.  Under the explicit
support-containment hypothesis connecting fluctuation dependencies to the
declared active supports inside `Ω`, the target-cover Mayer integral factorizes
over the canonical confined Ω-components of its index set. -/
theorem mayerActivity_integral_factor_confinedComponentCoverFamily_of_fluctuationSupport_subset
    {Site β ι : Type*} [Fintype Site] [DecidableEq Site] [DecidableEq ι]
    [MeasurableSpace β] [Nonempty β]
    {Ψ : Site → Type*}
    (μ : Measure β) [IsProbabilityMeasure μ]
    (C : OmegaTargetCover Site ι)
    (H : ι → LocalActivity Site Ψ (fun _ => β) ℂ)
    (ψ : ∀ x, Ψ x)
    (hsub : ∀ i, i ∈ C.index →
      (H i).fluctuationSupport ⊆ C.omega ∩ C.activeSupport i) :
    let Γ := confinedComponents (omegaOverlapGraph C.omega C.activeSupport) C.index
    ∫ φ, (C.mayerActivity H).globalEval ψ φ
        ∂(Measure.pi fun _ : Site => μ)
      =
      Γ.attach.prod fun D =>
        ∫ φ, ((OmegaConnectedCover.confinedComponentCoverFamily
              C.omega C.activeSupport C.index D).mayerActivity H).globalEval
            ψ φ
          ∂(Measure.pi fun _ : Site => μ) := by
  simpa [OmegaTargetCover.mayerActivity, OmegaTargetCover.toConnectedCover] using
    OmegaConnectedCover.mayerActivity_integral_factor_confinedComponentCoverFamily_of_fluctuationSupport_subset
      μ C.omega C.activeSupport C.index H ψ hsub

end OmegaTargetCover

end YangMills.RG
