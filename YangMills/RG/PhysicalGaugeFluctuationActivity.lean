/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCovarianceLocalization
import YangMills.RG.LocalFunctional

/-!
# Source-facing physical gauge fluctuation activities

This module records the first API point after a localized covariance-root
certificate.  It does **not** construct the Balaban/CMP raw activity.  Instead
it fixes the shape a source theorem must provide:

* a covariance-root certificate for the Gaussian-coordinate map;
* a family of two-field local activities on physical bonds;
* explicit active-support containment;
* an explicit raw pointwise bound and a separate decay majorant;
* an explicit source-construction proposition linking the activity to the
  physical Hessian/fluctuation integral.

Thus the analytic content remains visible and unproved here.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Global physical coordinate fields on the positive-bond convention. -/
abbrev PhysicalGaugeField (d N Nc : ℕ) [NeZero N] :=
  PhysicalBond d N → SUNLieCoord Nc

/-- A two-field local activity on physical gauge coordinates. -/
abbrev PhysicalGaugeLocalActivity (d N Nc : ℕ) [NeZero N] :=
  LocalActivity (PhysicalBond d N)
    (fun _ => SUNLieCoord Nc) (fun _ => SUNLieCoord Nc) ℂ

/-- Source-facing pointwise raw bound for a family of physical gauge local
activities. -/
def PhysicalGaugeRawActivityBound
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (activity : ι → PhysicalGaugeLocalActivity d N Nc)
    (amplitude : ι → ℝ) : Prop :=
  ∀ X (ψ φ : PhysicalGaugeField d N Nc),
    ‖(activity X).globalEval ψ φ‖ ≤ amplitude X

/-- Source-facing decay majorant for the raw activity amplitudes. -/
def PhysicalGaugeActivityDecay
    {ι : Type*}
    (amplitude weight : ι → ℝ) (H0 : ℝ) : Prop :=
  ∀ X, amplitude X ≤ H0 * weight X

/-- A localized physical Gaussian fluctuation activity package.

The field `source_construction` is intentionally an external proposition: it
is where a future source theorem identifies the local activity with the actual
Balaban fluctuation integral after the change of variables `B' = C^{1/2} X`.
The fields `raw_bound` and `decay_bound` are also supplied, not proved here. -/
structure PhysicalLocalizedGaussianActivityCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (precision covariance root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (covNormBound rootNormBound : ℝ)
    (covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ)
    (activity : ι → PhysicalGaugeLocalActivity d N Nc)
    (activeSupport : ι → Finset (PhysicalBond d N))
    (amplitude weight : ι → ℝ)
    (H0 : ℝ)
    (sourceConstruction : Prop) : Prop where
  root_certificate :
    PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight
  source_construction :
    sourceConstruction
  spectator_support_subset :
    ∀ X, (activity X).spectatorSupport ⊆ activeSupport X
  fluctuation_support_subset :
    ∀ X, (activity X).fluctuationSupport ⊆ activeSupport X
  amplitude_nonneg :
    ∀ X, 0 ≤ amplitude X
  weight_nonneg :
    ∀ X, 0 ≤ weight X
  raw_bound :
    PhysicalGaugeRawActivityBound activity amplitude
  decay_bound :
    PhysicalGaugeActivityDecay amplitude weight H0

/-- Package source-supplied physical fluctuation activity data.

This constructor theorem is deliberately thin: it certifies that the data are
available in the shape downstream Appendix-F/CMP116 consumers need, while
leaving the Hessian expansion, change of variables, and analytic estimates as
source hypotheses. -/
theorem physicalLocalizedGaussianActivityCertificate_of_source
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {precision covariance root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {covNormBound rootNormBound H0 : ℝ}
    {covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ}
    {activity : ι → PhysicalGaugeLocalActivity d N Nc}
    {activeSupport : ι → Finset (PhysicalBond d N)}
    {amplitude weight : ι → ℝ}
    {sourceConstruction : Prop}
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource : sourceConstruction)
    (hspectator :
      ∀ X, (activity X).spectatorSupport ⊆ activeSupport X)
    (hfluctuation :
      ∀ X, (activity X).fluctuationSupport ⊆ activeSupport X)
    (hamplitude_nonneg : ∀ X, 0 ≤ amplitude X)
    (hweight_nonneg : ∀ X, 0 ≤ weight X)
    (hraw : PhysicalGaugeRawActivityBound activity amplitude)
    (hdecay : PhysicalGaugeActivityDecay amplitude weight H0) :
    PhysicalLocalizedGaussianActivityCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight activity activeSupport amplitude weight H0
      sourceConstruction := by
  exact
    { root_certificate := hroot
      source_construction := hsource
      spectator_support_subset := hspectator
      fluctuation_support_subset := hfluctuation
      amplitude_nonneg := hamplitude_nonneg
      weight_nonneg := hweight_nonneg
      raw_bound := hraw
      decay_bound := hdecay }

/-- A localized Gaussian activity certificate exposes the raw pointwise bound. -/
theorem physicalGaugeRawActivityBound_of_localizedGaussianActivityCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {precision covariance root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {covNormBound rootNormBound H0 : ℝ}
    {covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ}
    {activity : ι → PhysicalGaugeLocalActivity d N Nc}
    {activeSupport : ι → Finset (PhysicalBond d N)}
    {amplitude weight : ι → ℝ}
    {sourceConstruction : Prop}
    (hcert :
      PhysicalLocalizedGaussianActivityCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight activity activeSupport amplitude weight H0
        sourceConstruction) :
    PhysicalGaugeRawActivityBound activity amplitude :=
  hcert.raw_bound

/-- A localized Gaussian activity certificate exposes the combined raw
pointwise decay estimate. -/
theorem physicalGaugeRawActivityDecay_of_localizedGaussianActivityCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {precision covariance root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {covNormBound rootNormBound H0 : ℝ}
    {covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ}
    {activity : ι → PhysicalGaugeLocalActivity d N Nc}
    {activeSupport : ι → Finset (PhysicalBond d N)}
    {amplitude weight : ι → ℝ}
    {sourceConstruction : Prop}
    (hcert :
      PhysicalLocalizedGaussianActivityCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight activity activeSupport amplitude weight H0
        sourceConstruction) :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖(activity X).globalEval ψ φ‖ ≤ H0 * weight X := by
  intro X ψ φ
  exact (hcert.raw_bound X ψ φ).trans (hcert.decay_bound X)

end YangMills.RG
