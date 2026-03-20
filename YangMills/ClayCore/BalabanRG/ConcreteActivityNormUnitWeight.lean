import Mathlib
import YangMills.ClayCore.BalabanRG.ConcreteFiniteFullBridgeWeightedL1

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ConcreteActivityNormUnitWeight — (v1.0.12-alpha Phase 3)

Sanity layer for the weighted `L¹` architecture.

We instantiate the weight by the constant-one family
  w(j,p) = 1
and prove that the weighted construction recovers the previous plain `L¹` path.

This is deliberately conservative:
it does not yet introduce a physical polymer-size weight,
but it validates that the weighted framework properly extends the existing
concrete `L¹` development.
-/

noncomputable section

/-- Constant-one weight family. -/
def unitWeight (d : ℕ) : ∀ j, Polymer d (Int.ofNat j) → ℝ :=
  fun _ _ => 1

theorem unitWeight_nonneg (d : ℕ) : ∀ j p, 0 ≤ unitWeight d j p := by
  intro j p
  simp [unitWeight]

theorem unitWeight_ge_one (d : ℕ) : ∀ j p, 1 ≤ unitWeight d j p := by
  intro j p
  simp [unitWeight]

section Recovery

variable {d : ℕ}
variable {k : ℕ}
variable [Fintype (Polymer d (Int.ofNat k))]
variable [DecidableEq (Polymer d (Int.ofNat k))]

/-- Weighted `L¹` with unit weight is the plain `L¹` norm. 0 sorrys. -/
theorem activityWeightedL1Norm_unit_eq_activityL1Norm
    (K : ActivityFamily d k) :
    activityWeightedL1Norm (d := d) (k := k) (unitWeight d k) K =
      activityL1Norm (d := d) (k := k) K := by
  unfold activityWeightedL1Norm unitWeight activityL1Norm
  simp

end Recovery

section EvaluationRecovery

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- The weighted evaluation bound under unit weight recovers the same constant-1
evaluation control. 0 sorrys. -/
theorem activityNormEvaluationBoundAt_unitWeight
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    ActivityNormEvaluationBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
  exact activityNormEvaluationBoundAt_weightedL1
    (d := d) (N_c := N_c)
    (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d) k p₀

/-- The weighted Cauchy evaluation bound under unit weight recovers the same
constant-1 Cauchy control. 0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_unitWeight
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    ActivityNormEvaluationCauchyBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
  exact activityNormEvaluationCauchyBoundAt_weightedL1
    (d := d) (N_c := N_c)
    (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d) k p₀

end EvaluationRecovery

section FiniteFullRecovery

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Unit weight yields a concrete weighted finite full large-field bound.
0 sorrys. -/
theorem finiteFullLargeFieldBound_unitWeight
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    FiniteFullLargeFieldBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
  exact finiteFullLargeFieldBound_weightedL1
    (d := d) (N_c := N_c)
    (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    k β hlargeA polys

/-- Unit weight yields a concrete weighted finite full Cauchy bound.
0 sorrys. -/
theorem finiteFullCauchyBound_unitWeight
    (k : ℕ) (β : ℝ)
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    FiniteFullCauchyBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
  exact finiteFullCauchyBound_weightedL1
    (d := d) (N_c := N_c)
    (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    k β hcauchyA polys

/-- Concrete weighted finite full control with unit weight. 0 sorrys. -/
def finiteCanonicalGeometricBridgeControlFull_unitWeight
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    RGViaBridgeControlFull d N_c k β := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
  exact finiteCanonicalGeometricBridgeControlFull_weightedL1
    (d := d) (N_c := N_c)
    (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    k β hlargeA hcauchyA polys

/-- High-level finite full consumer for the unit-weight weighted path.
0 sorrys. -/
theorem cauchy_decay_via_finite_full_bridge_control_unitWeight
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
    let ctrl := finiteCanonicalGeometricBridgeControlFull_unitWeight
      (d := d) (N_c := N_c) k β hlargeA hcauchyA polys
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) (unitWeight d) (unitWeight_nonneg d) (unitWeight_ge_one d)
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end FiniteFullRecovery

end

end YangMills.ClayCore
