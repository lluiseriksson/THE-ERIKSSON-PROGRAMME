/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalShellCombesThomasEndpoint

/-!
# The trivial `SUNAdjointModel` witness and full-chain non-vacuity of
`CT_fixedVolume`
(`hRpoly` campaign — P4-CT non-vacuity audit, external-review finding
2026-07-13)

**The finding (external static review of checkpoint `9120a23b`).**
`SUNAdjointModel Nc` is abstract orthogonal-action data in the chosen
`su(Nc)` coordinates, and the repository constructed NO instance of it —
so every physical-shell theorem quantifying over `ρ` had a formally
non-empty but unwitnessed hypothesis class.  This module closes the
non-vacuity half and REGISTERS the honest remainder:

* `trivialSUNAdjointModel` — the NAMED trivial witness `adCLM g := id`.
  This is NOT the SU(N) adjoint representation and is not sold as such.
  It is sufficient for the flat lane because at the TRIVIAL background the
  cochain operators only ever evaluate the model at `g = 1`, where EVERY
  model acts as the identity (`ad_one`); the flat-shell chain genuinely
  does not depend on the model choice.
* `sunAdjointModel_nonempty` — the hypothesis class of every `ρ`-generic
  shell theorem is inhabited.
* `CT_fixedVolume_nonvacuous` — the CAPSTONE audit: for every volume
  `(d, L, N', Nc)` and every `a > 0` there EXIST a model `ρ`, a
  fixed-volume Poincaré constant `CP`, and a POSITIVE rate `θ` such that
  the actual flat covariance satisfies the exponential kernel bound —
  every structural hypothesis of the Addendum-268 endpoint discharged by
  proved theorems (`exists_flatGaugeHodgePoincare` supplies `CP`;
  `exists_pos_tiltBudget` supplies `θ`).  No hypothesis class in the
  chain is empty.

**Registered open obligation (NOT discharged here).**  The TRUE matricial
adjoint model — `Ad(g)X = gXg⁻¹` on traceless anti-Hermitian matrices with
the trace inner product, transported to the `EuclideanSpace ℝ (Fin (Nc²−1))`
coordinates by an isometric basis identification — is required the moment
the background is non-trivial (the interacting lane).  It is registered in
`docs/HRPOLY-CAMPAIGN-PLAN.md` §3ter as the P4-ADJ item and is NOT claimed
by this module.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

/-- **The trivial adjoint model, named as such**: every group element acts
as the identity.  This inhabits the model class and is exact for the flat
(trivial-background) lane, where only `adCLM 1` is ever consumed; it is NOT
the SU(N) adjoint representation. -/
noncomputable def trivialSUNAdjointModel (Nc : ℕ) [NeZero Nc] :
    SUNAdjointModel Nc where
  adCLM _ := ContinuousLinearMap.id ℝ (SUNLieCoord Nc)
  ad_one := rfl
  ad_mul _ _ := by
    ext x
    rfl
  ad_inner _ _ _ := rfl

/-- Every `ρ`-generic physical-shell theorem has an inhabited hypothesis
class. -/
theorem sunAdjointModel_nonempty (Nc : ℕ) [NeZero Nc] :
    Nonempty (SUNAdjointModel Nc) :=
  ⟨trivialSUNAdjointModel Nc⟩

/-- **Full-chain non-vacuity of `CT_fixedVolume`**: for every volume
`(d, L, N', Nc)` and every `a > 0` there exist a model, a fixed-volume
Poincaré constant, and a POSITIVE tilt rate for which the actual flat
physical covariance at the `zeroSigma` free shell satisfies the
source-facing exponential kernel bound.  Every structural hypothesis of
the Addendum-268 endpoint is discharged by a proved theorem; nothing in
the chain is instantiated on an empty class. -/
theorem CT_fixedVolume_nonvacuous
    (d L N' Nc : ℕ)
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]
    {a : ℝ} (ha : 0 < a) :
    ∃ (ρ : SUNAdjointModel Nc) (CP : ℝ)
      (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP) (θ : ℝ),
      0 < θ ∧
      PhysicalCovarianceExponentialKernelBound
        (flatGaugeFixedCovarianceCLM ρ (fun i : Empty => i.elim)
          (fun i : Empty => i.elim) ha hP zeroSigma_delta_summable
          zeroSigma_norm_le (zeroSigma_budget ρ ha hP))
        physicalBondDist (2 / (min 1 a / CP)) θ := by
  obtain ⟨CP, hP⟩ :=
    exists_flatGaugeHodgePoincare
      (d := d) (L := L) (N' := N') (Nc := Nc) (trivialSUNAdjointModel Nc)
  obtain ⟨θ, hθ, hker⟩ :=
    exists_flatGaugeFixedCovariance_CT_fixedVolume
      (trivialSUNAdjointModel Nc) ha hP
  exact ⟨trivialSUNAdjointModel Nc, CP, hP, θ, hθ, hker⟩

end YangMills.RG
