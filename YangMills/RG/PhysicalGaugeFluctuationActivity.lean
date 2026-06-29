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

namespace PhysicalGaugeRawActivityDecay

/-- Transport a physical raw-activity decay estimate along a pointwise
domination of weights.

This is source bookkeeping only: if a component estimate is proved with a
native source weight and that source weight is dominated by the downstream
consumer weight, the same amplitude works for the downstream weight. -/
theorem mono_weight
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity : ι → PhysicalGaugeLocalActivity d N Nc}
    {weight sourceWeight : ι → ℝ} {H0 : ℝ}
    (hdecay : PhysicalGaugeRawActivityDecay activity sourceWeight H0)
    (hH0 : 0 ≤ H0)
    (sourceWeight_le : ∀ X, sourceWeight X ≤ weight X) :
    PhysicalGaugeRawActivityDecay activity weight H0 := by
  intro X ψ φ
  exact
    (hdecay X ψ φ).trans
      (mul_le_mul_of_nonneg_left (sourceWeight_le X) hH0)

/-- Transport a physical raw-activity decay estimate along a scalar amplitude
comparison.

This is the companion to `mono_weight`: sources may prove a component estimate
with a sharper constant than the one reserved by the downstream budget. -/
theorem mono_amplitude
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity : ι → PhysicalGaugeLocalActivity d N Nc}
    {weight : ι → ℝ} {H0 H1 : ℝ}
    (hdecay : PhysicalGaugeRawActivityDecay activity weight H0)
    (hH : H0 ≤ H1)
    (weight_nonneg : ∀ X, 0 ≤ weight X) :
    PhysicalGaugeRawActivityDecay activity weight H1 := by
  intro X ψ φ
  exact
    (hdecay X ψ φ).trans
      (mul_le_mul_of_nonneg_right hH (weight_nonneg X))

/-- Transport a physical raw-activity decay estimate along both a pointwise
weight domination and a scalar amplitude comparison. -/
theorem mono
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity : ι → PhysicalGaugeLocalActivity d N Nc}
    {weight sourceWeight : ι → ℝ} {H0 H1 : ℝ}
    (hdecay : PhysicalGaugeRawActivityDecay activity sourceWeight H0)
    (hH0 : 0 ≤ H0)
    (hH : H0 ≤ H1)
    (sourceWeight_le : ∀ X, sourceWeight X ≤ weight X)
    (weight_nonneg : ∀ X, 0 ≤ weight X) :
    PhysicalGaugeRawActivityDecay activity weight H1 :=
  (hdecay.mono_weight hH0 sourceWeight_le).mono_amplitude
    hH weight_nonneg

end PhysicalGaugeRawActivityDecay

/-- Build the flexible Dimock E/R/B certificate from component estimates proved
against a source-native weight, once that weight is dominated by the downstream
certificate weight.

The theorem only transports weights in already supplied component decays.  It
does not prove the component estimates, the E/R/B decomposition, or any
Yang--Mills source theorem. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_weightDomination
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight weight : ι → ℝ} {Hdelta Hr Hb H0 : ℝ}
    (weight_nonneg : ∀ X, 0 ≤ weight X)
    (sourceWeight_le : ∀ X, sourceWeight X ≤ weight X)
    (hHdelta : 0 ≤ Hdelta)
    (hHr : 0 ≤ Hr)
    (hHb : 0 ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE sourceWeight Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc sourceWeight Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc sourceWeight Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc weight Hdelta Hr Hb H0 :=
  PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays
    weight_nonneg
    component_budget
    decomposes
    (deltaE_decay.mono_weight hHdelta sourceWeight_le)
    (rloc_decay.mono_weight hHr sourceWeight_le)
    (bloc_decay.mono_weight hHb sourceWeight_le)

/-- Exponential weight domination from an already-linearized rate/metric
comparison.

This is the scalar transport used when a source estimate is written in a
native source metric, while the downstream Dimock/Balaban consumer uses a
different exponential metric and pays one global `exp kappa` loss.  All
geometric/source content is kept in the explicit comparison hypothesis. -/
theorem weight_domination_of_rate_metric_comparison
    {X : Type*}
    {sourceMetric balabanMetric : X → X → ℝ}
    {rhoSrc rhoDimock kappa : ℝ}
    (hcmp :
      ∀ x y,
        rhoDimock * balabanMetric x y ≤
          rhoSrc * sourceMetric x y + kappa) :
    ∀ x y,
      Real.exp (-(rhoSrc * sourceMetric x y)) ≤
        Real.exp kappa *
          Real.exp (-(rhoDimock * balabanMetric x y)) := by
  intro x y
  have hlog :
      -(rhoSrc * sourceMetric x y) ≤
        kappa + -(rhoDimock * balabanMetric x y) := by
    linarith [hcmp x y]
  calc
    Real.exp (-(rhoSrc * sourceMetric x y))
        ≤ Real.exp (kappa + -(rhoDimock * balabanMetric x y)) :=
          Real.exp_le_exp.mpr hlog
    _ =
        Real.exp kappa *
          Real.exp (-(rhoDimock * balabanMetric x y)) := by
      rw [Real.exp_add]

/-- Project-facing alias for the same scalar exponential transport.

Callers that have already proved the combined domination/rate-margin
comparison can use this name without committing to a concrete source dictionary
inside this module. -/
theorem weight_domination_of_domination_and_rate_margin
    {X : Type*}
    {sourceMetric balabanMetric : X → X → ℝ}
    {rhoSrc rhoDimock kappa : ℝ}
    (hcmp :
      ∀ x y,
        rhoDimock * balabanMetric x y ≤
          rhoSrc * sourceMetric x y + kappa) :
    ∀ x y,
      Real.exp (-(rhoSrc * sourceMetric x y)) ≤
        Real.exp kappa *
          Real.exp (-(rhoDimock * balabanMetric x y)) :=
  weight_domination_of_rate_metric_comparison hcmp

/-- Scalar budget transport for the Appendix-F shifted source weight.

If the source constants `Hdelta`, `Hr`, and `Hb` fit under a witnessed budget
`H0`, then after paying the single shifted-metric factor `exp kappa` all three
component budgets still fit under `exp kappa * H0`. -/
theorem dimock318_expShifted_componentBudget
    {kappa Hdelta Hr Hb H0 : ℝ}
    (component_budget : Hdelta + Hr + Hb ≤ H0) :
    Real.exp kappa * Hdelta + Real.exp kappa * Hr +
        Real.exp kappa * Hb ≤ Real.exp kappa * H0 := by
  calc
    Real.exp kappa * Hdelta + Real.exp kappa * Hr +
        Real.exp kappa * Hb =
        Real.exp kappa * (Hdelta + Hr + Hb) := by ring
    _ ≤ Real.exp kappa * H0 :=
      mul_le_mul_of_nonneg_left component_budget (Real.exp_nonneg kappa)

/-- Build the flexible Dimock E/R/B certificate after paying the Appendix-F
shifted-metric factor.

This is the source-facing form for a Dimock/CMP116 three-piece budget whose
native constants are `Hdelta`, `Hr`, and `Hb`, but whose Appendix-F consumer
uses the shifted weight and hence the amplitudes `exp kappa * _`.  The analytic
component estimates remain explicit premises; this theorem only discharges the
shared scalar budget transport. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_expShiftedBudget
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {weight : ι → ℝ} {kappa Hdelta Hr Hb H0 : ℝ}
    (weight_nonneg : ∀ X, 0 ≤ weight X)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (decomposes :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (activity X).globalEval ψ φ =
          (deltaE X).globalEval ψ φ +
            (rloc X).globalEval ψ φ +
            (bloc X).globalEval ψ φ)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE weight
        (Real.exp kappa * Hdelta))
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc weight
        (Real.exp kappa * Hr))
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc weight
        (Real.exp kappa * Hb)) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc weight
      (Real.exp kappa * Hdelta)
      (Real.exp kappa * Hr)
      (Real.exp kappa * Hb)
      (Real.exp kappa * H0) := by
  exact
    PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays
      weight_nonneg
      (dimock318_expShifted_componentBudget component_budget)
      decomposes
      deltaE_decay
      rloc_decay
      bloc_decay

/-- Definitional-sum variant of `of_componentDecays`.

When the source construction defines the total local activity as the literal
local sum of the `deltaE`, `Rloc`, and `Bloc` pieces, the E/R/B decomposition
dictionary is discharged by the local-activity algebra rather than carried as a
separate hypothesis. -/
theorem PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays_localActivitySum
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {weight : ι → ℝ} {Hdelta Hr Hb H0 : ℝ}
    (weight_nonneg : ∀ X, 0 ≤ weight X)
    (component_budget : Hdelta + Hr + Hb ≤ H0)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE weight Hdelta)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc weight Hr)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc weight Hb) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      (fun X => ((deltaE X).add (rloc X)).add (bloc X))
      deltaE rloc bloc weight Hdelta Hr Hb H0 := by
  exact
    PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays
      weight_nonneg
      component_budget
      (by
        intro X ψ φ
        simp)
      deltaE_decay
      rloc_decay
      bloc_decay

/-- A finite source-level sum of local activity components inherits a raw
decay estimate from componentwise raw decays and a scalar budget.

This is the finite-term analogue of the E/R/B certificates above: when a source
defines the activity as `LocalActivity.finsetSum I component`, the activity
decomposition and triangle inequality are handled here, while every analytic
component estimate remains an explicit premise. -/
theorem physicalGaugeRawActivityDecay_of_finsetSum_componentDecays
    {κ ι : Type*} {d N Nc : ℕ} [NeZero N]
    {I : Finset κ}
    {component : κ → ι → PhysicalGaugeLocalActivity d N Nc}
    {weight : ι → ℝ} {H : κ → ℝ} {H0 : ℝ}
    (weight_nonneg : ∀ X, 0 ≤ weight X)
    (component_budget : (∑ i ∈ I, H i) ≤ H0)
    (component_decay :
      ∀ i, i ∈ I →
        PhysicalGaugeRawActivityDecay (component i) weight (H i)) :
    PhysicalGaugeRawActivityDecay
      (fun X => LocalActivity.finsetSum I (fun i => component i X))
      weight H0 := by
  intro X ψ φ
  rw [LocalActivity.globalEval_finsetSum]
  calc
    ‖∑ i ∈ I, (component i X).globalEval ψ φ‖ ≤
        ∑ i ∈ I, ‖(component i X).globalEval ψ φ‖ := by
      simpa using
        (norm_sum_le
          (s := I)
          (f := fun i => (component i X).globalEval ψ φ))
    _ ≤ ∑ i ∈ I, H i * weight X := by
      exact
        Finset.sum_le_sum
          (by
            intro i hi
            exact component_decay i hi X ψ φ)
    _ = (∑ i ∈ I, H i) * weight X := by
      rw [Finset.sum_mul]
    _ ≤ H0 * weight X :=
      mul_le_mul_of_nonneg_right component_budget (weight_nonneg X)

/-- A finite source-level sum of local activity components inherits a raw
amplitude bound from componentwise raw amplitude bounds. -/
theorem physicalGaugeRawActivityBound_of_finsetSum_componentBounds
    {κ ι : Type*} {d N Nc : ℕ} [NeZero N]
    {I : Finset κ}
    {component : κ → ι → PhysicalGaugeLocalActivity d N Nc}
    {amplitude : κ → ι → ℝ}
    (component_bound :
      ∀ i, i ∈ I →
        PhysicalGaugeRawActivityBound (component i) (amplitude i)) :
    PhysicalGaugeRawActivityBound
      (fun X => LocalActivity.finsetSum I (fun i => component i X))
      (fun X => ∑ i ∈ I, amplitude i X) := by
  intro X ψ φ
  rw [LocalActivity.globalEval_finsetSum]
  calc
    ‖∑ i ∈ I, (component i X).globalEval ψ φ‖ ≤
        ∑ i ∈ I, ‖(component i X).globalEval ψ φ‖ := by
      simpa using
        (norm_sum_le
          (s := I)
          (f := fun i => (component i X).globalEval ψ φ))
    _ ≤ ∑ i ∈ I, amplitude i X := by
      exact
        Finset.sum_le_sum
          (by
            intro i hi
            exact component_bound i hi X ψ φ)

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

/-- Finite-source-sum constructor for localized Gaussian activity
certificates.

If a source theorem defines the physical local activity as a finite sum of
local components, this constructor derives the finite-sum support and raw
amplitude bound from termwise source data.  The analytic component bounds and
the final decay majorant remain explicit premises. -/
theorem physicalLocalizedGaussianActivityCertificate_of_finsetSum_source
    {κ ι : Type*} {d N Nc : ℕ} [NeZero N]
    {precision covariance root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {covNormBound rootNormBound H0 : ℝ}
    {covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ}
    {I : Finset κ}
    {component : κ → ι → PhysicalGaugeLocalActivity d N Nc}
    {activeSupport : ι → Finset (PhysicalBond d N)}
    {amplitude : κ → ι → ℝ}
    {weight : ι → ℝ}
    {sourceConstruction : Prop}
    (hroot :
      PhysicalLocalizedCovarianceRootCertificate
        precision covariance root covNormBound rootNormBound covWeight
        rootWeight)
    (hsource : sourceConstruction)
    (hspectator :
      ∀ i, i ∈ I → ∀ X, (component i X).spectatorSupport ⊆ activeSupport X)
    (hfluctuation :
      ∀ i, i ∈ I → ∀ X, (component i X).fluctuationSupport ⊆ activeSupport X)
    (hamplitude_nonneg : ∀ i, i ∈ I → ∀ X, 0 ≤ amplitude i X)
    (hweight_nonneg : ∀ X, 0 ≤ weight X)
    (hraw :
      ∀ i, i ∈ I →
        PhysicalGaugeRawActivityBound (component i) (amplitude i))
    (hdecay :
      PhysicalGaugeActivityDecay
        (fun X => ∑ i ∈ I, amplitude i X) weight H0) :
    PhysicalLocalizedGaussianActivityCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight
      (fun X => LocalActivity.finsetSum I (fun i => component i X))
      activeSupport
      (fun X => ∑ i ∈ I, amplitude i X)
      weight H0 sourceConstruction := by
  refine
    physicalLocalizedGaussianActivityCertificate_of_source
      hroot hsource ?hspectator ?hfluctuation ?hamplitude_nonneg
      hweight_nonneg ?hraw hdecay
  · intro X
    exact
      LocalActivity.spectatorSupport_finsetSum_subset
        (fun i hi => hspectator i hi X)
  · intro X
    exact
      LocalActivity.fluctuationSupport_finsetSum_subset
        (fun i hi => hfluctuation i hi X)
  · intro X
    exact
      Finset.sum_nonneg
        (by
          intro i hi
          exact hamplitude_nonneg i hi X)
  · exact physicalGaugeRawActivityBound_of_finsetSum_componentBounds hraw

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
