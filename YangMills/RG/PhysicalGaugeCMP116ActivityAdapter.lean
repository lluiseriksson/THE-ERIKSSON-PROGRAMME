/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeFluctuationActivity
import YangMills.RG.BalabanCMP116KsharpAdapter

/-!
# Physical gauge activities to CMP116 raw activity hypotheses

This module is a deliberately thin bridge.  It does not construct the physical
Balaban/CMP116 activity from the gauge-fixed Hessian, and it does not prove
localization of the covariance square root.  Instead it records the exact
transport obligations a source theorem must provide in order to turn the
source-facing physical localized-Gaussian activity certificate into the
CMP116/Appendix-F `hraw` and support hypotheses already consumed downstream.

The nonlocal covariance-root information remains hidden only behind explicit
fields:

* a physical localized-Gaussian activity certificate;
* a CMP116 localized-activity family;
* spectator/fluctuation field transports from CMP116 coordinates to physical
  positive-bond fields;
* exact preservation of `globalEval` under those transports;
* active-support localization inside the Appendix-F skeleton;
* domination of the physical decay weight by the Appendix-F exponential weight.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Source-facing transport package from a physical localized Gaussian activity
certificate to a CMP116 localized activity family.

All analytic and geometric content is explicit data here.  A future source
theorem has to instantiate this record by identifying the CMP116 local
activity with the physical fluctuation integral after the change of variables
`B' = C^{1/2} X`, proving the support localization, and supplying the weight
domination. -/
structure PhysicalGaugeCMP116ActivityTransport
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc)
    (covNormBound rootNormBound : ℝ)
    (covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N))
    (amplitude weight : OmegaPolymerType HF z → ℝ)
    (H0 κ : ℝ)
    (sourceConstruction : Prop) where
  certificate :
    PhysicalLocalizedGaussianActivityCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight physicalActivity physicalActiveSupport amplitude weight H0
      sourceConstruction
  family :
    BalabanCMP116LocalizedActivityFamily
      (Cube d L) lieDim Ψ (OmegaPolymerType HF z)
  spectatorTransport :
    (∀ b : Cube d L, Ψ b) → PhysicalGaugeField dPhys N Nc
  fluctuationTransport :
    (∀ _ : Cube d L, Fin lieDim → Real) → PhysicalGaugeField dPhys N Nc
  globalEval_eq :
    ∀ X ψ φ,
      (family.activity X).globalEval ψ φ =
        (physicalActivity X).globalEval
          (spectatorTransport ψ) (fluctuationTransport φ)
  activeSupport_subset_skeleton :
    ∀ X, X ∈ Λ → family.activeSupport X ⊆ skeleton HF X.val
  weight_domination :
    ∀ X, X ∈ Λ → weight X ≤ appendixFHoleExpWeight HF κ X.val

/-- The source transport package immediately supplies the CMP116 Appendix-F
support hypotheses. -/
theorem physicalGaugeCMP116SupportHypotheses_of_transport
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction) :
    BalabanCMP116AppendixFSupportHypotheses
      (lieDim := lieDim) (Ψ := Ψ) HF z Λ T.family := by
  exact
    BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_subset_skeleton
      T.activeSupport_subset_skeleton

/-- The source transport package converts the physical localized-Gaussian
raw-decay estimate into the CMP116 `hraw` shape consumed by Appendix F. -/
theorem balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport
    {dPhys N Nc d L : ℕ} [NeZero N] [NeZero L]
    {lieDim : Nat} {Ψ : Cube d L → Type*}
    {HF : HoleFamily d L}
    {z : Finset (Cube d L) → ℂ}
    {Λ : Finset (OmegaPolymerType HF z)}
    {precision covariance root :
      PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
        PhysicalGaugeOneCochain dPhys N Nc}
    {covNormBound rootNormBound H0 κ : ℝ}
    {covWeight rootWeight :
      PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ}
    {physicalActivity :
      OmegaPolymerType HF z → PhysicalGaugeLocalActivity dPhys N Nc}
    {physicalActiveSupport :
      OmegaPolymerType HF z → Finset (PhysicalBond dPhys N)}
    {amplitude weight : OmegaPolymerType HF z → ℝ}
    {sourceConstruction : Prop}
    (T :
      PhysicalGaugeCMP116ActivityTransport (lieDim := lieDim) (Ψ := Ψ) HF z Λ
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight physicalActivity physicalActiveSupport amplitude weight
        H0 κ sourceConstruction)
    (hH0 : 0 ≤ H0) :
    ∀ (ψ : ∀ b : Cube d L, Ψ b)
      (φ : ∀ _ : Cube d L, Fin lieDim → Real) X, X ∈ Λ →
      ‖(T.family.activity X).globalEval ψ φ‖ ≤
        H0 * appendixFHoleExpWeight HF κ X.val := by
  intro ψ φ X hX
  calc
    ‖(T.family.activity X).globalEval ψ φ‖ =
        ‖(physicalActivity X).globalEval
          (T.spectatorTransport ψ) (T.fluctuationTransport φ)‖ := by
      rw [T.globalEval_eq X ψ φ]
    _ ≤ H0 * weight X :=
      physicalGaugeRawActivityDecay_of_localizedGaussianActivityCertificate
        T.certificate X (T.spectatorTransport ψ) (T.fluctuationTransport φ)
    _ ≤ H0 * appendixFHoleExpWeight HF κ X.val :=
      mul_le_mul_of_nonneg_left (T.weight_domination X hX) hH0

end YangMills.RG
