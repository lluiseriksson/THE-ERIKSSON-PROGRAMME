/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116OperatorTransport
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

/-- Source-facing combined raw decay for physical gauge local activities. -/
def PhysicalGaugeRawActivityDecay
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (activity : ι → PhysicalGaugeLocalActivity d N Nc)
    (weight : ι → ℝ) (H0 : ℝ) : Prop :=
  ∀ X (ψ φ : PhysicalGaugeField d N Nc),
    ‖(activity X).globalEval ψ φ‖ ≤ H0 * weight X

/-- Source-facing decay majorant for the raw activity amplitudes. -/
def PhysicalGaugeActivityDecay
    {ι : Type*}
    (amplitude weight : ι → ℝ) (H0 : ℝ) : Prop :=
  ∀ X, amplitude X ≤ H0 * weight X

private theorem norm_complex_three_add_le (a b c : ℂ) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc
    ‖a + b + c‖ = ‖(a + b) + c‖ := rfl
    _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
    _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
      linarith [norm_add_le a b]
    _ = ‖a‖ + ‖b‖ + ‖c‖ := by ring

/-- Source-facing three-piece input certificate for the Dimock Lemma 3.18
assembly pattern.

The certificate does not prove the source estimates.  It records the exact
shape needed to replace one monolithic physical raw decay assumption by three
component estimates: localized `deltaE`, localized `R`, and boundary `B`, each
with one third of the target budget. -/
structure PhysicalGaugeDimock318ThreePieceCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc)
    (weight : ι → ℝ) (H0 : ℝ) : Prop where
  decomposes :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      (activity X).globalEval ψ φ =
        (deltaE X).globalEval ψ φ +
          (rloc X).globalEval ψ φ +
          (bloc X).globalEval ψ φ
  deltaE_bound :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖(deltaE X).globalEval ψ φ‖ ≤ (H0 / 3) * weight X
  rloc_bound :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖(rloc X).globalEval ψ φ‖ ≤ (H0 / 3) * weight X
  bloc_bound :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖(bloc X).globalEval ψ φ‖ ≤ (H0 / 3) * weight X

/-- Source-facing three-piece input certificate with source-supplied component
budgets.

This is the flexible-budget variant of
`PhysicalGaugeDimock318ThreePieceCertificate`.  It is meant for primary sources
that bound the localized `deltaE`, localized `R`, and boundary `B` pieces with
constants that are not literally one third of the final target budget. -/
structure PhysicalGaugeDimock318FlexibleBudgetCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc)
    (weight : ι → ℝ) (Hdelta Hr Hb H0 : ℝ) : Prop where
  weight_nonneg :
    ∀ X, 0 ≤ weight X
  component_budget :
    Hdelta + Hr + Hb ≤ H0
  decomposes :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      (activity X).globalEval ψ φ =
        (deltaE X).globalEval ψ φ +
          (rloc X).globalEval ψ φ +
          (bloc X).globalEval ψ φ
  deltaE_bound :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖(deltaE X).globalEval ψ φ‖ ≤ Hdelta * weight X
  rloc_bound :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖(rloc X).globalEval ψ φ‖ ≤ Hr * weight X
  bloc_bound :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖(bloc X).globalEval ψ φ‖ ≤ Hb * weight X

/-- Build the flexible Dimock three-piece certificate from the existing
component-wise physical raw-decay predicate.

This keeps the source theorem at the component level: callers may prove decay
for `deltaE`, `Rloc`, and `Bloc` separately using
`PhysicalGaugeRawActivityDecay`, then supply only the activity decomposition and
the scalar budget comparison. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {weight : ι → ℝ} {Hdelta Hr Hb H0 : ℝ}
    (weight_nonneg : ∀ X, 0 ≤ weight X)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE weight Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc weight Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc weight Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc weight Hdelta Hr Hb H0 where
  weight_nonneg := weight_nonneg
  component_budget := component_budget
  decomposes := decomposes
  deltaE_bound := deltaE_decay
  rloc_bound := rloc_decay
  bloc_bound := bloc_decay

/-- The Dimock Lemma 3.18 three-piece certificate exposes the combined
physical raw pointwise decay estimate. -/
theorem physicalGaugeRawActivityDecay_of_dimock318ThreePieceCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {weight : ι → ℝ} {H0 : ℝ}
    (hcert :
      PhysicalGaugeDimock318ThreePieceCertificate
        activity deltaE rloc bloc weight H0) :
    PhysicalGaugeRawActivityDecay activity weight H0 := by
  intro X ψ φ
  rw [hcert.decomposes X ψ φ]
  let a := (deltaE X).globalEval ψ φ
  let b := (rloc X).globalEval ψ φ
  let c := (bloc X).globalEval ψ φ
  calc
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
      norm_complex_three_add_le a b c
    _ ≤ (H0 / 3) * weight X + (H0 / 3) * weight X +
        (H0 / 3) * weight X := by
      exact
        add_le_add
          (add_le_add (hcert.deltaE_bound X ψ φ) (hcert.rloc_bound X ψ φ))
          (hcert.bloc_bound X ψ φ)
    _ = H0 * weight X := by ring

/-- A flexible-budget Dimock three-piece certificate exposes the combined
physical raw pointwise decay estimate whenever the component budgets add up to
the target budget. -/
theorem physicalGaugeRawActivityDecay_of_dimock318FlexibleBudgetCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {weight : ι → ℝ} {Hdelta Hr Hb H0 : ℝ}
    (hcert :
      PhysicalGaugeDimock318FlexibleBudgetCertificate
        activity deltaE rloc bloc weight Hdelta Hr Hb H0) :
    PhysicalGaugeRawActivityDecay activity weight H0 := by
  intro X ψ φ
  rw [hcert.decomposes X ψ φ]
  let a := (deltaE X).globalEval ψ φ
  let b := (rloc X).globalEval ψ φ
  let c := (bloc X).globalEval ψ φ
  calc
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
      norm_complex_three_add_le a b c
    _ ≤ Hdelta * weight X + Hr * weight X + Hb * weight X := by
      exact
        add_le_add
          (add_le_add (hcert.deltaE_bound X ψ φ) (hcert.rloc_bound X ψ φ))
          (hcert.bloc_bound X ψ φ)
    _ = (Hdelta + Hr + Hb) * weight X := by ring
    _ ≤ H0 * weight X :=
      mul_le_mul_of_nonneg_right hcert.component_budget
        (hcert.weight_nonneg X)

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

/-- A localized Gaussian activity certificate exposes spectator-support
containment. -/
theorem physicalGaugeSpectatorSupport_subset_of_localizedGaussianActivityCertificate
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
    ∀ X, (activity X).spectatorSupport ⊆ activeSupport X :=
  hcert.spectator_support_subset

/-- A localized Gaussian activity certificate exposes fluctuation-support
containment. -/
theorem physicalGaugeFluctuationSupport_subset_of_localizedGaussianActivityCertificate
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
    ∀ X, (activity X).fluctuationSupport ⊆ activeSupport X :=
  hcert.fluctuation_support_subset

/-- A localized Gaussian activity certificate exposes amplitude
nonnegativity. -/
theorem physicalGaugeAmplitude_nonneg_of_localizedGaussianActivityCertificate
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
    ∀ X, 0 ≤ amplitude X :=
  hcert.amplitude_nonneg

/-- A localized Gaussian activity certificate exposes weight nonnegativity. -/
theorem physicalGaugeWeight_nonneg_of_localizedGaussianActivityCertificate
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
    ∀ X, 0 ≤ weight X :=
  hcert.weight_nonneg

/-- A localized Gaussian activity certificate exposes the separate amplitude
decay majorant. -/
theorem physicalGaugeActivityDecay_of_localizedGaussianActivityCertificate
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
    PhysicalGaugeActivityDecay amplitude weight H0 :=
  hcert.decay_bound

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
    PhysicalGaugeRawActivityDecay activity weight H0 := by
  intro X ψ φ
  exact (hcert.raw_bound X ψ φ).trans (hcert.decay_bound X)

end YangMills.RG
