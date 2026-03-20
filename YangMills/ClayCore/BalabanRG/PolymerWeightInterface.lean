import Mathlib
import YangMills.ClayCore.BalabanRG.ConcreteActivityNormUnitWeight

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerWeightInterface — (v1.0.13-alpha Phase 1)

Abstract interface for polymer weights used by weighted activity norms.

This phase is deliberately conservative:
- define an abstract polymer weight at a fixed scale,
- define a family of polymer weights across all scales,
- record the two minimal assumptions already used by the weighted `L¹` path:
  nonnegativity and `1 ≤ w`,
- provide wrappers showing that the existing weighted `L¹` machinery factors
  through this interface,
- package the constant-one weight family as the first canonical example.

This prepares the next phase, where we can plug in genuinely nontrivial
polymer-size or geometry-based weights without changing the bridge API again.
-/

noncomputable section

/-! ## Basic interface -/

/-- Weight on polymers at a fixed scale. -/
abbrev PolymerWeight (d k : ℕ) :=
  Polymer d (Int.ofNat k) → ℝ

/-- Weight family across all scales. -/
abbrev PolymerWeightFamily (d : ℕ) :=
  ∀ j, PolymerWeight d j

/-- Fixed-scale nonnegativity. -/
def PolymerWeightNonneg (d k : ℕ)
    (w : PolymerWeight d k) : Prop :=
  ∀ p, 0 ≤ w p

/-- Fixed-scale lower bound `1 ≤ w`. -/
def PolymerWeightGeOne (d k : ℕ)
    (w : PolymerWeight d k) : Prop :=
  ∀ p, 1 ≤ w p

/-- Family nonnegativity. -/
def PolymerWeightFamilyNonneg (d : ℕ)
    (w : PolymerWeightFamily d) : Prop :=
  ∀ j p, 0 ≤ w j p

/-- Family lower bound `1 ≤ w`. -/
def PolymerWeightFamilyGeOne (d : ℕ)
    (w : PolymerWeightFamily d) : Prop :=
  ∀ j p, 1 ≤ w j p

/-! ## Canonical basepoint: unit weight -/

/-- Constant-one polymer weight family. -/
abbrev unitPolymerWeightFamily (d : ℕ) : PolymerWeightFamily d :=
  unitWeight d

theorem unitPolymerWeightFamily_nonneg (d : ℕ) :
    PolymerWeightFamilyNonneg d (unitPolymerWeightFamily d) :=
  unitWeight_nonneg d

theorem unitPolymerWeightFamily_ge_one (d : ℕ) :
    PolymerWeightFamilyGeOne d (unitPolymerWeightFamily d) :=
  unitWeight_ge_one d

/-! ## Weighted ActivityNorm through the abstract interface -/

section WeightedNorm

variable {d : ℕ}
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- The weighted `ActivityNorm` family obtained from an abstract polymer weight
interface. 0 sorrys. -/
instance instActivityNormFromPolymerWeight
    (w : PolymerWeightFamily d)
    (hw_nonneg : PolymerWeightFamilyNonneg d w)
    (hw_ge_one : PolymerWeightFamilyGeOne d w) :
    ∀ j, ActivityNorm d j :=
  instActivityNormWeightedL1All (d := d) w hw_nonneg hw_ge_one

end WeightedNorm

/-! ## Native evaluation/Cauchy wrappers -/

section EvaluationWrappers

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Evaluation bound from the abstract polymer weight interface. 0 sorrys. -/
theorem activityNormEvaluationBoundAt_of_polymerWeight
    (w : PolymerWeightFamily d)
    (hw_nonneg : PolymerWeightFamilyNonneg d w)
    (hw_ge_one : PolymerWeightFamilyGeOne d w)
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
    ActivityNormEvaluationBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
  exact activityNormEvaluationBoundAt_weightedL1
    (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k p₀

/-- Cauchy evaluation bound from the abstract polymer weight interface.
0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_of_polymerWeight
    (w : PolymerWeightFamily d)
    (hw_nonneg : PolymerWeightFamilyNonneg d w)
    (hw_ge_one : PolymerWeightFamilyGeOne d w)
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
    ActivityNormEvaluationCauchyBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
  exact activityNormEvaluationCauchyBoundAt_weightedL1
    (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k p₀

end EvaluationWrappers

/-! ## Finite full wrappers -/

section FiniteFullWrappers

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Finite full large-field bound from the abstract polymer weight interface.
0 sorrys. -/
theorem finiteFullLargeFieldBound_of_polymerWeight
    (w : PolymerWeightFamily d)
    (hw_nonneg : PolymerWeightFamilyNonneg d w)
    (hw_ge_one : PolymerWeightFamilyGeOne d w)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
    FiniteFullLargeFieldBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
  exact finiteFullLargeFieldBound_weightedL1
    (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hlargeA polys

/-- Finite full Cauchy bound from the abstract polymer weight interface.
0 sorrys. -/
theorem finiteFullCauchyBound_of_polymerWeight
    (w : PolymerWeightFamily d)
    (hw_nonneg : PolymerWeightFamilyNonneg d w)
    (hw_ge_one : PolymerWeightFamilyGeOne d w)
    (k : ℕ) (β : ℝ)
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
    FiniteFullCauchyBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
  exact finiteFullCauchyBound_weightedL1
    (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hcauchyA polys

/-- Concrete finite full control from the abstract polymer weight interface.
0 sorrys. -/
def finiteCanonicalGeometricBridgeControlFull_of_polymerWeight
    (w : PolymerWeightFamily d)
    (hw_nonneg : PolymerWeightFamilyNonneg d w)
    (hw_ge_one : PolymerWeightFamilyGeOne d w)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
    RGViaBridgeControlFull d N_c k β := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
  exact finiteCanonicalGeometricBridgeControlFull_weightedL1
    (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hlargeA hcauchyA polys

/-- High-level finite full consumer from the abstract polymer weight interface.
0 sorrys. -/
theorem cauchy_decay_via_finite_full_bridge_control_of_polymerWeight
    (w : PolymerWeightFamily d)
    (hw_nonneg : PolymerWeightFamilyNonneg d w)
    (hw_ge_one : PolymerWeightFamilyGeOne d w)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
    let ctrl := finiteCanonicalGeometricBridgeControlFull_of_polymerWeight
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hlargeA hcauchyA polys
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight (d := d) w hw_nonneg hw_ge_one
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end FiniteFullWrappers

/-! ## Sanity: specialize the interface to the unit weight family -/

section UnitWeightRecovery

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Unit-weight evaluation wrapper. 0 sorrys. -/
theorem activityNormEvaluationBoundAt_unitPolymerWeight
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight
        (d := d) (unitPolymerWeightFamily d)
        (unitPolymerWeightFamily_nonneg d)
        (unitPolymerWeightFamily_ge_one d)
    ActivityNormEvaluationBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight
      (d := d) (unitPolymerWeightFamily d)
      (unitPolymerWeightFamily_nonneg d)
      (unitPolymerWeightFamily_ge_one d)
  exact activityNormEvaluationBoundAt_of_polymerWeight
    (d := d) (N_c := N_c)
    (unitPolymerWeightFamily d)
    (unitPolymerWeightFamily_nonneg d)
    (unitPolymerWeightFamily_ge_one d)
    k p₀

/-- Unit-weight finite full consumer wrapper. 0 sorrys. -/
theorem cauchy_decay_via_finite_full_bridge_control_unitPolymerWeight
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromPolymerWeight
        (d := d) (unitPolymerWeightFamily d)
        (unitPolymerWeightFamily_nonneg d)
        (unitPolymerWeightFamily_ge_one d)
    let ctrl := finiteCanonicalGeometricBridgeControlFull_of_polymerWeight
      (d := d) (N_c := N_c)
      (unitPolymerWeightFamily d)
      (unitPolymerWeightFamily_nonneg d)
      (unitPolymerWeightFamily_ge_one d)
      k β hlargeA hcauchyA polys
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromPolymerWeight
      (d := d) (unitPolymerWeightFamily d)
      (unitPolymerWeightFamily_nonneg d)
      (unitPolymerWeightFamily_ge_one d)
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end UnitWeightRecovery

end

end YangMills.ClayCore
