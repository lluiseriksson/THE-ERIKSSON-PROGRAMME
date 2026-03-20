import Mathlib
import YangMills.ClayCore.BalabanRG.FullCauchySingletonBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ActivityNormEvaluationBound — (v1.0.9-alpha Phase 1)

This file isolates the exact missing analytic interface behind the
singleton pointwise bridge.

Recon summary:
- `ActivityNorm.dist_nonneg` exists,
- but no native evaluation-vs-dist lemma was found,
- so we name the exact evaluation assumptions we eventually want
  to discharge from the analytic theory.

This does not yet prove the analytic estimates.
It pins down their cleanest API-facing formulation.
-/

noncomputable section

/-- Evaluation at a fixed polymer is controlled by `A * dist(K,0)`. -/
def ActivityNormEvaluationBoundAt (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (A : ℝ)
    (p₀ : Polymer d (Int.ofNat k)) : Prop :=
  ∀ (K : ActivityFamily d k),
    |K p₀| ≤ A * ActivityNorm.dist K (fun _ => 0)

/-- Evaluation differences at a fixed polymer are controlled by
`A * dist(K₁,K₂)`. -/
def ActivityNormEvaluationCauchyBoundAt (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) (A : ℝ)
    (p₀ : Polymer d (Int.ofNat k)) : Prop :=
  ∀ (K₁ K₂ : ActivityFamily d k),
    |K₁ p₀ - K₂ p₀| ≤ A * ActivityNorm.dist K₁ K₂

/-- Native evaluation control implies the singleton pointwise large-field
bridge hypothesis. 0 sorrys. -/
theorem singletonPointwiseBound_of_activityNormEvaluationBoundAt
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (h : ActivityNormEvaluationBoundAt d N_c k A p₀) :
    SingletonPointwiseBound d N_c k A p₀ :=
  h

/-- Native evaluation control implies the singleton pointwise Cauchy
bridge hypothesis. 0 sorrys. -/
theorem singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (h : ActivityNormEvaluationCauchyBoundAt d N_c k A p₀) :
    SingletonPointwiseCauchyBound d N_c k A p₀ :=
  h

/-- Automatic singleton full control from native ActivityNorm evaluation
bounds and scalar comparisons. 0 sorrys. -/
def singletonCanonicalGeometricBridgeControlFull_of_activityNormEvaluationBounds
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β A_large A_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : ActivityNormEvaluationBoundAt d N_c k A_large p₀)
    (hlargeA : A_large ≤ Real.exp (-β))
    (hcauchy : ActivityNormEvaluationCauchyBoundAt d N_c k A_cauchy p₀)
    (hcauchyA : A_cauchy ≤ physicalContractionRate β) :
    RGViaBridgeControlFull d N_c k β :=
  singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
    k β A_large A_cauchy p₀
    (singletonPointwiseBound_of_activityNormEvaluationBoundAt
      (d := d) (N_c := N_c) k A_large p₀ hlarge)
    hlargeA
    (singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
      (d := d) (N_c := N_c) k A_cauchy p₀ hcauchy)
    hcauchyA

/-- Large-field extractor from native ActivityNorm evaluation data.
0 sorrys. -/
theorem activityNormEvaluation_singleton_control_large_field
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β A_large A_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : ActivityNormEvaluationBoundAt d N_c k A_large p₀)
    (hlargeA : A_large ≤ Real.exp (-β))
    (hcauchy : ActivityNormEvaluationCauchyBoundAt d N_c k A_cauchy p₀)
    (hcauchyA : A_cauchy ≤ physicalContractionRate β)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |(singletonCanonicalGeometricBridgeControlFull_of_activityNormEvaluationBounds
        k β A_large A_cauchy p₀ hlarge hlargeA hcauchy hcauchyA).core.bridge.fieldOfActivity K x| ≤
      Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) :=
  singleton_pointwise_bounds_control_large_field
    k β A_large A_cauchy p₀
    (singletonPointwiseBound_of_activityNormEvaluationBoundAt
      (d := d) (N_c := N_c) k A_large p₀ hlarge)
    hlargeA
    (singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
      (d := d) (N_c := N_c) k A_cauchy p₀ hcauchy)
    hcauchyA
    K x

/-- Cauchy extractor from native ActivityNorm evaluation data.
0 sorrys. -/
theorem activityNormEvaluation_singleton_control_cauchy
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β A_large A_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : ActivityNormEvaluationBoundAt d N_c k A_large p₀)
    (hlargeA : A_large ≤ Real.exp (-β))
    (hcauchy : ActivityNormEvaluationCauchyBoundAt d N_c k A_cauchy p₀)
    (hcauchyA : A_cauchy ≤ physicalContractionRate β)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |(singletonCanonicalGeometricBridgeControlFull_of_activityNormEvaluationBounds
        k β A_large A_cauchy p₀ hlarge hlargeA hcauchy hcauchyA).core.bridge.fieldOfActivity K₁ x -
      (singletonCanonicalGeometricBridgeControlFull_of_activityNormEvaluationBounds
        k β A_large A_cauchy p₀ hlarge hlargeA hcauchy hcauchyA).core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂ :=
  singleton_pointwise_bounds_control_cauchy
    k β A_large A_cauchy p₀
    (singletonPointwiseBound_of_activityNormEvaluationBoundAt
      (d := d) (N_c := N_c) k A_large p₀ hlarge)
    hlargeA
    (singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
      (d := d) (N_c := N_c) k A_cauchy p₀ hcauchy)
    hcauchyA
    K₁ K₂ x

/-- Zero-field extractor from native ActivityNorm evaluation data.
0 sorrys. -/
theorem activityNormEvaluation_singleton_control_zero_field
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β A_large A_cauchy : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (hlarge : ActivityNormEvaluationBoundAt d N_c k A_large p₀)
    (hlargeA : A_large ≤ Real.exp (-β))
    (hcauchy : ActivityNormEvaluationCauchyBoundAt d N_c k A_cauchy p₀)
    (hcauchyA : A_cauchy ≤ physicalContractionRate β) :
    (singletonCanonicalGeometricBridgeControlFull_of_activityNormEvaluationBounds
      k β A_large A_cauchy p₀ hlarge hlargeA hcauchy hcauchyA).core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 :=
  singleton_pointwise_bounds_control_zero_field
    k β A_large A_cauchy p₀
    (singletonPointwiseBound_of_activityNormEvaluationBoundAt
      (d := d) (N_c := N_c) k A_large p₀ hlarge)
    hlargeA
    (singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
      (d := d) (N_c := N_c) k A_cauchy p₀ hcauchy)
    hcauchyA

/-- High-level consumer from native ActivityNorm evaluation singleton data.
0 sorrys. -/
theorem cauchy_decay_from_activityNormEvaluation_singleton_data
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k A_large A_cauchy : ℝ)
    (p₀ : Polymer d (Int.ofNat 0))
    (hlarge : ActivityNormEvaluationBoundAt d N_c 0 A_large p₀)
    (hlargeA : A_large ≤ Real.exp (-β_k))
    (hcauchy : ActivityNormEvaluationCauchyBoundAt d N_c 0 A_cauchy p₀)
    (hcauchyA : A_cauchy ≤ physicalContractionRate β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ))
    (x : BalabanFiniteSite d 0) :
    let ctrl := singletonCanonicalGeometricBridgeControlFull_of_activityNormEvaluationBounds
      0 β_k A_large A_cauchy p₀ hlarge hlargeA hcauchy hcauchyA
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β_k) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β_k * ActivityNorm.dist K₁ K₂) := by
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end

end YangMills.ClayCore
