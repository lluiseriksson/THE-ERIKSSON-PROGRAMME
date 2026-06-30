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

/-- Source-facing E/R/B component boundary for Dimock Lemma 3.18 packaging.

This record deliberately stores only source-native data: the E/R/B
decomposition, the three component decays against the source weight, and
nonnegativity of the source component amplitudes.  Downstream choices such as
the final weight, amplitude relaxation, and total component budget remain
inputs to the eliminator. -/
structure PhysicalGaugeDimock318ERBComponentBoundary
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc)
    (sourceWeight : ι → ℝ)
    (HdeltaSrc HrSrc HbSrc : ℝ) : Prop where
  HdeltaSrc_nonneg :
    0 ≤ HdeltaSrc
  HrSrc_nonneg :
    0 ≤ HrSrc
  HbSrc_nonneg :
    0 ≤ HbSrc
  decomposes :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      (activity X).globalEval ψ φ =
        (deltaE X).globalEval ψ φ +
          (rloc X).globalEval ψ φ +
          (bloc X).globalEval ψ φ
  deltaE_decay :
    PhysicalGaugeRawActivityDecay deltaE sourceWeight HdeltaSrc
  rloc_decay :
    PhysicalGaugeRawActivityDecay rloc sourceWeight HrSrc
  bloc_decay :
    PhysicalGaugeRawActivityDecay bloc sourceWeight HbSrc

/-- Source-facing E/R/B decomposition shape for CMP119 Eq. (2.23) and the
CMP122-II post-R update Eq. (1.101).

This only names the Lean shape of the decomposition dictionary: the source
activity evaluates as the sum of its `deltaE`, local-`R`, and B/local pieces.
It does not prove the Balaban action-notation dictionary or identify the
physical activity with the source construction. -/
def CMP119CMP122ERBDecomposition
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc) : Prop :=
  ∀ X (ψ φ : PhysicalGaugeField d N Nc),
    (activity X).globalEval ψ φ =
      (deltaE X).globalEval ψ φ +
        (rloc X).globalEval ψ φ +
        (bloc X).globalEval ψ φ

/-- Project the named CMP119/CMP122 E/R/B decomposition shape to the raw
`decomposes` field expected by the boundary record. -/
theorem cmp119CMP122ERBDecomposition_decomposes
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    (h :
      CMP119CMP122ERBDecomposition
        activity deltaE rloc bloc) :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      (activity X).globalEval ψ φ =
        (deltaE X).globalEval ψ φ +
          (rloc X).globalEval ψ φ +
          (bloc X).globalEval ψ φ :=
  h

/-- Source-native E/R/B decomposition before the Balaban/CMP action notation is
identified with the Lean local-activity representation.

This separates the paper-side scalar identity from the dictionaries that map
the total, `deltaE`, local-`R`, and B/local source terms to
`PhysicalGaugeLocalActivity.globalEval`.  It is intended for the CMP119/CMP122
post-R decomposition route, where using CMP119 action notation directly as a
Lean physical activity would be too strong without the post-R dictionary. -/
structure CMP119CMP122ERBSourceDecomposition
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (sourceEval sourceDelta sourceRloc sourceBloc :
      ι → PhysicalGaugeField d N Nc → PhysicalGaugeField d N Nc → ℂ) : Prop where
  decomposes :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      sourceEval X ψ φ =
        sourceDelta X ψ φ +
          sourceRloc X ψ φ +
          sourceBloc X ψ φ

namespace CMP119CMP122ERBSourceDecomposition

/-- Convert a paper-native CMP119/CMP122 E/R/B source decomposition into the
Lean decomposition predicate, provided all four source scalar terms have been
identified with the corresponding Lean local activities. -/
theorem to_ERBDecomposition
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {sourceEval sourceDelta sourceRloc sourceBloc :
      ι → PhysicalGaugeField d N Nc → PhysicalGaugeField d N Nc → ℂ}
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    (h :
      CMP119CMP122ERBSourceDecomposition
        sourceEval sourceDelta sourceRloc sourceBloc)
    (activity_identification :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (activity X).globalEval ψ φ = sourceEval X ψ φ)
    (deltaE_identification :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (deltaE X).globalEval ψ φ = sourceDelta X ψ φ)
    (rloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (rloc X).globalEval ψ φ = sourceRloc X ψ φ)
    (bloc_identification :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (bloc X).globalEval ψ φ = sourceBloc X ψ φ) :
    CMP119CMP122ERBDecomposition activity deltaE rloc bloc := by
  intro X ψ φ
  calc
    (activity X).globalEval ψ φ = sourceEval X ψ φ :=
      activity_identification X ψ φ
    _ =
        sourceDelta X ψ φ +
          sourceRloc X ψ φ +
          sourceBloc X ψ φ :=
      h.decomposes X ψ φ
    _ =
        (deltaE X).globalEval ψ φ +
          (rloc X).globalEval ψ φ +
          (bloc X).globalEval ψ φ := by
      rw [← deltaE_identification X ψ φ,
        ← rloc_identification X ψ φ,
        ← bloc_identification X ψ φ]

end CMP119CMP122ERBSourceDecomposition

/-- Source-facing B/local component boundary for Dimock Lemma 3.18 packaging.

This is the one-component companion to
`PhysicalGaugeDimock318ERBComponentBoundary`: it records only the native
B/local amplitude nonnegativity and the component decay against the chosen
source weight.  CMP119/CMP122 still have to theorem-feed the actual component
decay and the dictionary identifying their B/local term with the Lean `bloc`
activity. -/
structure PhysicalGaugeDimock318BLocalComponentBoundary
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (bloc : ι → PhysicalGaugeLocalActivity d N Nc)
    (sourceWeight : ι → ℝ) (HbSrc : ℝ) : Prop where
  HbSrc_nonneg :
    0 ≤ HbSrc
  bloc_decay :
    PhysicalGaugeRawActivityDecay bloc sourceWeight HbSrc

/-- Native exponential source weight shape for the CMP119 B/local component
bound.

The source metric is deliberately abstract: the CMP119/CMP122 dictionary still
has to identify Balaban's polymer distance with the Lean metric used here. -/
noncomputable def cmp119BLocalWeight
    {ι : Type*}
    (kappaB : ℝ) (sourceMetric : ι → ℝ) (X : ι) : ℝ :=
  Real.exp (-(kappaB * sourceMetric X))

/-- The CMP119 B/local source weight is nonnegative. -/
theorem cmp119BLocalWeight_nonneg
    {ι : Type*}
    (kappaB : ℝ) (sourceMetric : ι → ℝ) (X : ι) :
    0 ≤ cmp119BLocalWeight kappaB sourceMetric X :=
  Real.exp_nonneg _

/-- Metric domination sufficient condition for comparing two native CMP119
B/local weights.

If the target Lean metric is bounded by the source-paper metric and the decay
rate is nonnegative, then the source-paper exponential weight is bounded by the
target Lean exponential weight. -/
theorem cmp119BLocalWeight_le_of_metric_domination
    {ι : Type*}
    {sourceMetric targetMetric : ι → ℝ} {kappaB : ℝ}
    (targetMetric_le_sourceMetric :
      ∀ X, targetMetric X ≤ sourceMetric X)
    (kappaB_nonneg :
      0 ≤ kappaB) :
    ∀ X,
      cmp119BLocalWeight kappaB sourceMetric X ≤
        cmp119BLocalWeight kappaB targetMetric X := by
  intro X
  unfold cmp119BLocalWeight
  exact Real.exp_le_exp.mpr
    (neg_le_neg
      (mul_le_mul_of_nonneg_left
        (targetMetric_le_sourceMetric X) kappaB_nonneg))

/-- Source-facing CMP119 Eq. (2.42) B/local bound before the source-to-Lean
activity and metric dictionaries are applied.

The `sourceEval` field is the paper-native B/local term as a scalar function of
the two physical fields.  A later dictionary must identify it with
`(bloc X).globalEval ψ φ` and transport the paper metric to the Lean metric used
by `CMP119BLocalActivityEstimate`. -/
structure CMP119BLocalSourceBound
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (sourceEval :
      ι → PhysicalGaugeField d N Nc → PhysicalGaugeField d N Nc → ℂ)
    (sourceMetric : ι → ℝ) (HbSrc kappaB : ℝ) : Prop where
  bound :
    ∀ X (ψ φ : PhysicalGaugeField d N Nc),
      ‖sourceEval X ψ φ‖ ≤
        HbSrc * cmp119BLocalWeight kappaB sourceMetric X

/-- Source-facing B/local component estimate shape for CMP119 Eq. (2.42).

This is only the Lean shape of the source claim: a `bloc` activity is bounded by
a native B/local amplitude times an exponential polymer-local weight.  It does
not prove the CMP119 estimate or the dictionary identifying the paper's B/local
term with the Lean `bloc` activity. -/
def CMP119BLocalActivityEstimate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    (bloc : ι → PhysicalGaugeLocalActivity d N Nc)
    (sourceMetric : ι → ℝ) (HbSrc kappaB : ℝ) : Prop :=
  ∀ X (ψ φ : PhysicalGaugeField d N Nc),
    ‖(bloc X).globalEval ψ φ‖ ≤
      HbSrc * cmp119BLocalWeight kappaB sourceMetric X

namespace CMP119BLocalSourceBound

/-- Convert a source-native CMP119 B/local bound into the Lean
`CMP119BLocalActivityEstimate` shape, provided the source activity is identified
with the Lean `bloc` activity and the source weight is dominated by the target
Lean weight.

This theorem is dictionary plumbing only: Eq. (2.42), the B/local activity
identification, and the metric/weight domination are all explicit inputs. -/
theorem to_activityEstimate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {sourceEval :
      ι → PhysicalGaugeField d N Nc → PhysicalGaugeField d N Nc → ℂ}
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceMetric targetMetric : ι → ℝ} {HbSrc kappaB : ℝ}
    (h :
      CMP119BLocalSourceBound
        sourceEval sourceMetric HbSrc kappaB)
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (activity_identification :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (bloc X).globalEval ψ φ = sourceEval X ψ φ)
    (sourceWeight_le_target :
      ∀ X,
        cmp119BLocalWeight kappaB sourceMetric X ≤
          cmp119BLocalWeight kappaB targetMetric X) :
    CMP119BLocalActivityEstimate
      bloc targetMetric HbSrc kappaB := by
  intro X ψ φ
  calc
    ‖(bloc X).globalEval ψ φ‖ = ‖sourceEval X ψ φ‖ := by
      rw [activity_identification X ψ φ]
    _ ≤ HbSrc * cmp119BLocalWeight kappaB sourceMetric X :=
      h.bound X ψ φ
    _ ≤ HbSrc * cmp119BLocalWeight kappaB targetMetric X := by
      exact mul_le_mul_of_nonneg_left
        (sourceWeight_le_target X) HbSrc_nonneg

/-- Metric-domination specialization of `to_activityEstimate`.

This is the common CMP119 dictionary shape: a paper-native metric dominates the
Lean target metric, and the B/local decay rate is nonnegative. -/
theorem to_activityEstimate_of_metric_domination
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {sourceEval :
      ι → PhysicalGaugeField d N Nc → PhysicalGaugeField d N Nc → ℂ}
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceMetric targetMetric : ι → ℝ} {HbSrc kappaB : ℝ}
    (h :
      CMP119BLocalSourceBound
        sourceEval sourceMetric HbSrc kappaB)
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (activity_identification :
      ∀ X (ψ φ : PhysicalGaugeField d N Nc),
        (bloc X).globalEval ψ φ = sourceEval X ψ φ)
    (targetMetric_le_sourceMetric :
      ∀ X, targetMetric X ≤ sourceMetric X)
    (kappaB_nonneg :
      0 ≤ kappaB) :
    CMP119BLocalActivityEstimate
      bloc targetMetric HbSrc kappaB :=
  h.to_activityEstimate
    HbSrc_nonneg
    activity_identification
    (cmp119BLocalWeight_le_of_metric_domination
      targetMetric_le_sourceMetric kappaB_nonneg)

end CMP119BLocalSourceBound

/-- Convert the CMP119 B/local estimate shape into the raw-decay predicate used
by the component-boundary record. -/
theorem cmp119BLocal_rawActivityDecay
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceMetric : ι → ℝ} {HbSrc kappaB : ℝ}
    (hB :
      CMP119BLocalActivityEstimate
        bloc sourceMetric HbSrc kappaB) :
    PhysicalGaugeRawActivityDecay
      bloc (cmp119BLocalWeight kappaB sourceMetric) HbSrc := by
  simpa [PhysicalGaugeRawActivityDecay,
    CMP119BLocalActivityEstimate] using hB

namespace PhysicalGaugeDimock318BLocalComponentBoundary

/-- Project a B/local component boundary to the raw-decay predicate consumed by
the full E/R/B boundary. -/
theorem to_rawActivityDecay
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight : ι → ℝ} {HbSrc : ℝ}
    (h :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc sourceWeight HbSrc) :
    PhysicalGaugeRawActivityDecay bloc sourceWeight HbSrc :=
  h.bloc_decay

/-- Build the B/local boundary from the CMP119 Eq. (2.42)-shaped component
estimate.

The estimate remains an explicit premise; this theorem only packages it into the
boundary record consumed by the E/R/B assembly. -/
theorem of_cmp119BLocalActivityEstimate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceMetric : ι → ℝ} {HbSrc kappaB : ℝ}
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (hB :
      CMP119BLocalActivityEstimate
        bloc sourceMetric HbSrc kappaB) :
    PhysicalGaugeDimock318BLocalComponentBoundary
      bloc (cmp119BLocalWeight kappaB sourceMetric) HbSrc where
  HbSrc_nonneg := HbSrc_nonneg
  bloc_decay := cmp119BLocal_rawActivityDecay hB

end PhysicalGaugeDimock318BLocalComponentBoundary

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

namespace PhysicalGaugeDimock318BLocalComponentBoundary

/-- Transport a B/local component boundary along a pointwise domination of
weights, keeping the same source amplitude.

This is bookkeeping for downstream consumers: it proves no CMP119 B/local
estimate, but lets a supplied B/local boundary feed a larger weight budget. -/
theorem mono_weight
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight weight : ι → ℝ} {HbSrc : ℝ}
    (h :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc sourceWeight HbSrc)
    (sourceWeight_le : ∀ X, sourceWeight X ≤ weight X) :
    PhysicalGaugeDimock318BLocalComponentBoundary
      bloc weight HbSrc where
  HbSrc_nonneg := h.HbSrc_nonneg
  bloc_decay :=
    h.bloc_decay.mono_weight h.HbSrc_nonneg sourceWeight_le

/-- Transport a B/local component boundary along an amplitude relaxation.

The source weight nonnegativity is explicit because the B/local boundary record
stores only the component amplitude nonnegativity, not a downstream weight
budget. -/
theorem mono_amplitude
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight : ι → ℝ} {HbSrc HbDst : ℝ}
    (h :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc sourceWeight HbSrc)
    (HbSrc_le : HbSrc ≤ HbDst)
    (sourceWeight_nonneg : ∀ X, 0 ≤ sourceWeight X) :
    PhysicalGaugeDimock318BLocalComponentBoundary
      bloc sourceWeight HbDst where
  HbSrc_nonneg := h.HbSrc_nonneg.trans HbSrc_le
  bloc_decay :=
    h.bloc_decay.mono_amplitude HbSrc_le sourceWeight_nonneg

/-- Transport a B/local component boundary along both a pointwise weight
domination and an amplitude relaxation. -/
theorem mono
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {bloc : ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight weight : ι → ℝ} {HbSrc HbDst : ℝ}
    (h :
      PhysicalGaugeDimock318BLocalComponentBoundary
        bloc sourceWeight HbSrc)
    (HbSrc_le : HbSrc ≤ HbDst)
    (sourceWeight_le : ∀ X, sourceWeight X ≤ weight X)
    (weight_nonneg : ∀ X, 0 ≤ weight X) :
    PhysicalGaugeDimock318BLocalComponentBoundary
      bloc weight HbDst where
  HbSrc_nonneg := h.HbSrc_nonneg.trans HbSrc_le
  bloc_decay :=
    h.bloc_decay.mono h.HbSrc_nonneg HbSrc_le
      sourceWeight_le weight_nonneg

end PhysicalGaugeDimock318BLocalComponentBoundary

namespace PhysicalGaugeDimock318ERBComponentBoundary

/-- Eliminate a source-native E/R/B component boundary into the downstream
flexible budget certificate.

The theorem transports each component decay both in weight and in amplitude,
then assembles the existing flexible certificate.  It proves no component
estimate and no E/R/B decomposition; both are fields of the boundary record. -/
theorem to_flexibleBudgetCertificate
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight weight : ι → ℝ}
    {HdeltaSrc HrSrc HbSrc Hdelta Hr Hb H0 : ℝ}
    (h :
      PhysicalGaugeDimock318ERBComponentBoundary
        activity deltaE rloc bloc sourceWeight
        HdeltaSrc HrSrc HbSrc)
    (weight_nonneg : ∀ X, 0 ≤ weight X)
    (sourceWeight_le : ∀ X, sourceWeight X ≤ weight X)
    (HdeltaSrc_le : HdeltaSrc ≤ Hdelta)
    (HrSrc_le : HrSrc ≤ Hr)
    (HbSrc_le : HbSrc ≤ Hb)
    (component_budget : Hdelta + Hr + Hb ≤ H0) :
    PhysicalGaugeDimock318FlexibleBudgetCertificate
      activity deltaE rloc bloc weight Hdelta Hr Hb H0 :=
  PhysicalGaugeDimock318FlexibleBudgetCertificate.of_componentDecays
    weight_nonneg
    component_budget
    h.decomposes
    (h.deltaE_decay.mono
      h.HdeltaSrc_nonneg HdeltaSrc_le sourceWeight_le weight_nonneg)
    (h.rloc_decay.mono
      h.HrSrc_nonneg HrSrc_le sourceWeight_le weight_nonneg)
    (h.bloc_decay.mono
      h.HbSrc_nonneg HbSrc_le sourceWeight_le weight_nonneg)

/-- Build the E/R/B boundary from the named CMP119/CMP122 decomposition shape
and separately supplied component decays.

This theorem only routes the named source-facing decomposition dictionary into
the boundary record.  The component decays, source-amplitude nonnegativity, and
the source-to-Lean activity dictionary all remain explicit inputs. -/
theorem of_cmp119CMP122ERBDecomposition_componentDecays
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {activity deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight : ι → ℝ} {HdeltaSrc HrSrc HbSrc : ℝ}
    (HdeltaSrc_nonneg :
      0 ≤ HdeltaSrc)
    (HrSrc_nonneg :
      0 ≤ HrSrc)
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (decomposes :
      CMP119CMP122ERBDecomposition activity deltaE rloc bloc)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE sourceWeight HdeltaSrc)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc sourceWeight HrSrc)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc sourceWeight HbSrc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      activity deltaE rloc bloc sourceWeight HdeltaSrc HrSrc HbSrc where
  HdeltaSrc_nonneg := HdeltaSrc_nonneg
  HrSrc_nonneg := HrSrc_nonneg
  HbSrc_nonneg := HbSrc_nonneg
  decomposes :=
    cmp119CMP122ERBDecomposition_decomposes decomposes
  deltaE_decay := deltaE_decay
  rloc_decay := rloc_decay
  bloc_decay := bloc_decay

/-- Definitional-sum source boundary for the E/R/B component interface.

When the source construction defines the total local activity as the literal
local sum of its `deltaE`, `Rloc`, and `Bloc` pieces, the `decomposes` field of
`PhysicalGaugeDimock318ERBComponentBoundary` is discharged by local-activity
algebra.  The three component decays and their native amplitudes remain
explicit source obligations. -/
theorem of_componentDecays_localActivitySum
    {ι : Type*} {d N Nc : ℕ} [NeZero N]
    {deltaE rloc bloc :
      ι → PhysicalGaugeLocalActivity d N Nc}
    {sourceWeight : ι → ℝ} {HdeltaSrc HrSrc HbSrc : ℝ}
    (HdeltaSrc_nonneg :
      0 ≤ HdeltaSrc)
    (HrSrc_nonneg :
      0 ≤ HrSrc)
    (HbSrc_nonneg :
      0 ≤ HbSrc)
    (deltaE_decay :
      PhysicalGaugeRawActivityDecay deltaE sourceWeight HdeltaSrc)
    (rloc_decay :
      PhysicalGaugeRawActivityDecay rloc sourceWeight HrSrc)
    (bloc_decay :
      PhysicalGaugeRawActivityDecay bloc sourceWeight HbSrc) :
    PhysicalGaugeDimock318ERBComponentBoundary
      (fun X => ((deltaE X).add (rloc X)).add (bloc X))
      deltaE rloc bloc sourceWeight HdeltaSrc HrSrc HbSrc where
  HdeltaSrc_nonneg := HdeltaSrc_nonneg
  HrSrc_nonneg := HrSrc_nonneg
  HbSrc_nonneg := HbSrc_nonneg
  decomposes := by
    intro X ψ φ
    simp
  deltaE_decay := deltaE_decay
  rloc_decay := rloc_decay
  bloc_decay := bloc_decay

end PhysicalGaugeDimock318ERBComponentBoundary

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
