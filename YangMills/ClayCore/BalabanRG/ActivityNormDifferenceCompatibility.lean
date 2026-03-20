import Mathlib
import YangMills.ClayCore.BalabanRG.ActivityNormEvaluationBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ActivityNormDifferenceCompatibility — (v1.0.9-alpha Phase 3)

This file sharpens the remaining singleton analytic gap.

Phase 2 reduced singleton Cauchy control to:
1. one native evaluation-vs-dist bound, and
2. one structural compatibility statement
     dist(K₁ - K₂, 0) = dist(K₁, K₂).

In this phase, the structural compatibility is discharged from the native
definition of `ActivityNorm.dist` in `ActivitySpaceNorms`.

So the singleton Cauchy gap now reduces to just one genuinely analytic input:
a native evaluation-vs-dist bound.
-/

noncomputable section

/-- Structural compatibility of `ActivityNorm.dist` with subtraction. -/
def ActivityNormDifferenceCompatible (d N_c : ℕ) [NeZero N_c]
    [∀ j, ActivityNorm d j] (k : ℕ) : Prop :=
  ∀ (K₁ K₂ : ActivityFamily d k),
    ActivityNorm.dist (K₁ - K₂) (fun _ => 0) = ActivityNorm.dist K₁ K₂

/-- The structural compatibility is already true for the native ActivityNorm
distance. 0 sorrys. -/
theorem native_activityNormDifferenceCompatible
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) :
    ActivityNormDifferenceCompatible d N_c k := by
  intro K₁ K₂
  exact ActivityNorm.dist_sub_zero_eq_dist K₁ K₂

/-- Under subtraction-compatibility, a native evaluation-vs-dist bound implies
the native Cauchy evaluation bound. 0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_of_eval_and_differenceCompatible
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (heval : ActivityNormEvaluationBoundAt d N_c k A p₀)
    (hcompat : ActivityNormDifferenceCompatible d N_c k) :
    ActivityNormEvaluationCauchyBoundAt d N_c k A p₀ := by
  intro K₁ K₂
  calc
    |K₁ p₀ - K₂ p₀| = |(K₁ - K₂) p₀| := by
      rfl
    _ ≤ A * ActivityNorm.dist (K₁ - K₂) (fun _ => 0) := by
      exact heval (K₁ - K₂)
    _ = A * ActivityNorm.dist K₁ K₂ := by
      rw [hcompat K₁ K₂]

/-- The native singleton Cauchy evaluation bound now follows from a single
native evaluation-vs-dist bound. 0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_of_eval
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (heval : ActivityNormEvaluationBoundAt d N_c k A p₀) :
    ActivityNormEvaluationCauchyBoundAt d N_c k A p₀ :=
  activityNormEvaluationCauchyBoundAt_of_eval_and_differenceCompatible
    (d := d) (N_c := N_c) k A p₀ heval
    (native_activityNormDifferenceCompatible (d := d) (N_c := N_c) k)

/-- The pointwise singleton Cauchy bridge follows from one native evaluation
bound. 0 sorrys. -/
theorem singletonPointwiseCauchyBound_of_eval
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (heval : ActivityNormEvaluationBoundAt d N_c k A p₀) :
    SingletonPointwiseCauchyBound d N_c k A p₀ :=
  singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
    (d := d) (N_c := N_c) k A p₀
    (activityNormEvaluationCauchyBoundAt_of_eval
      (d := d) (N_c := N_c) k A p₀ heval)

/-- Under subtraction-compatibility, the pointwise singleton Cauchy bridge
follows from one native evaluation bound. 0 sorrys. -/
theorem singletonPointwiseCauchyBound_of_eval_and_differenceCompatible
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (heval : ActivityNormEvaluationBoundAt d N_c k A p₀)
    (hcompat : ActivityNormDifferenceCompatible d N_c k) :
    SingletonPointwiseCauchyBound d N_c k A p₀ :=
  singletonPointwiseCauchyBound_of_activityNormEvaluationCauchyBoundAt
    (d := d) (N_c := N_c) k A p₀
    (activityNormEvaluationCauchyBoundAt_of_eval_and_differenceCompatible
      (d := d) (N_c := N_c) k A p₀ heval hcompat)

/-- Full singleton control from a single native evaluation bound and the two
scalar comparisons. 0 sorrys. -/
def singletonCanonicalGeometricBridgeControlFull_of_eval
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (heval : ActivityNormEvaluationBoundAt d N_c k A p₀)
    (hlargeA : A ≤ Real.exp (-β))
    (hcauchyA : A ≤ physicalContractionRate β) :
    RGViaBridgeControlFull d N_c k β :=
  singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
    k β A A p₀
    (singletonPointwiseBound_of_activityNormEvaluationBoundAt
      (d := d) (N_c := N_c) k A p₀ heval)
    hlargeA
    (singletonPointwiseCauchyBound_of_eval
      (d := d) (N_c := N_c) k A p₀ heval)
    hcauchyA

/-- Full singleton control from a single native evaluation bound together with
distance/subtraction compatibility and the two scalar comparisons. 0 sorrys. -/
def singletonCanonicalGeometricBridgeControlFull_of_eval_and_differenceCompatible
    {d N_c : ℕ} [NeZero N_c] [∀ j, ActivityNorm d j]
    (k : ℕ) (β A : ℝ) (p₀ : Polymer d (Int.ofNat k))
    (heval : ActivityNormEvaluationBoundAt d N_c k A p₀)
    (hcompat : ActivityNormDifferenceCompatible d N_c k)
    (hlargeA : A ≤ Real.exp (-β))
    (hcauchyA : A ≤ physicalContractionRate β) :
    RGViaBridgeControlFull d N_c k β :=
  singletonCanonicalGeometricBridgeControlFull_of_pointwise_bounds
    k β A A p₀
    (singletonPointwiseBound_of_activityNormEvaluationBoundAt
      (d := d) (N_c := N_c) k A p₀ heval)
    hlargeA
    (singletonPointwiseCauchyBound_of_eval_and_differenceCompatible
      (d := d) (N_c := N_c) k A p₀ heval hcompat)
    hcauchyA

/-- High-level consumer from a single native evaluation bound. 0 sorrys. -/
theorem cauchy_decay_from_eval_singleton_data
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k A : ℝ)
    (p₀ : Polymer d (Int.ofNat 0))
    (heval : ActivityNormEvaluationBoundAt d N_c 0 A p₀)
    (hlargeA : A ≤ Real.exp (-β_k))
    (hcauchyA : A ≤ physicalContractionRate β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ))
    (x : BalabanFiniteSite d 0) :
    let ctrl := singletonCanonicalGeometricBridgeControlFull_of_eval
      0 β_k A p₀ heval hlargeA hcauchyA
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β_k) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β_k * ActivityNorm.dist K₁ K₂) := by
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

/-- High-level consumer from a single native evaluation bound plus
distance/subtraction compatibility. 0 sorrys. -/
theorem cauchy_decay_from_eval_and_differenceCompatible_singleton_data
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k A : ℝ)
    (p₀ : Polymer d (Int.ofNat 0))
    (heval : ActivityNormEvaluationBoundAt d N_c 0 A p₀)
    (hcompat : ActivityNormDifferenceCompatible d N_c 0)
    (hlargeA : A ≤ Real.exp (-β_k))
    (hcauchyA : A ≤ physicalContractionRate β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ))
    (x : BalabanFiniteSite d 0) :
    let ctrl := singletonCanonicalGeometricBridgeControlFull_of_eval_and_differenceCompatible
      0 β_k A p₀ heval hcompat hlargeA hcauchyA
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β_k) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β_k * ActivityNorm.dist K₁ K₂) := by
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

/-- Zero-field extractor for the single-evaluation singleton data package.
0 sorrys. -/
theorem zero_field_from_eval_singleton_data
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k A : ℝ)
    (p₀ : Polymer d (Int.ofNat 0))
    (heval : ActivityNormEvaluationBoundAt d N_c 0 A p₀)
    (hlargeA : A ≤ Real.exp (-β_k))
    (hcauchyA : A ≤ physicalContractionRate β_k) :
    let ctrl := singletonCanonicalGeometricBridgeControlFull_of_eval
      0 β_k A p₀ heval hlargeA hcauchyA
    ctrl.core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 := by
  intro ctrl
  exact rg_control_full_zero_field ctrl

/-- Zero-field extractor for the reduced singleton data package. 0 sorrys. -/
theorem zero_field_from_eval_and_differenceCompatible_singleton_data
    {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (β_k A : ℝ)
    (p₀ : Polymer d (Int.ofNat 0))
    (heval : ActivityNormEvaluationBoundAt d N_c 0 A p₀)
    (hcompat : ActivityNormDifferenceCompatible d N_c 0)
    (hlargeA : A ≤ Real.exp (-β_k))
    (hcauchyA : A ≤ physicalContractionRate β_k) :
    let ctrl := singletonCanonicalGeometricBridgeControlFull_of_eval_and_differenceCompatible
      0 β_k A p₀ heval hcompat hlargeA hcauchyA
    ctrl.core.bridge.fieldOfActivity (fun _ => 0) = fun _ => 0 := by
  intro ctrl
  exact rg_control_full_zero_field ctrl

end

end YangMills.ClayCore
