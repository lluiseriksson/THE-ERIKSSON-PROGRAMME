import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerWeightInterface

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# PolymerSizeWeight — (v1.0.13-alpha Phase 2)

First genuinely nontrivial concrete polymer weight.

We use the native combinatorial size already present in the repository:

  Polymer.size X = X.sites.card

and lift it to a polymer weight family

  w_k(X) = |X|.

This phase is deliberately conservative:
- define the size weight family,
- prove the minimal interface facts `0 ≤ w` and `1 ≤ w`,
- instantiate the existing abstract weight-interface wrappers,
- validate that the weighted evaluation and finite-full bridge machinery
  works with this first nontrivial weight.

No new bridge architecture is introduced here; we only plug a real weight
into the interface created in v1.0.13-alpha Phase 1.
-/

noncomputable section

/-! ## Concrete size weight -/

/-- Native size weight family:
`w_k(X) = |X| = X.sites.card`. -/
abbrev sizeWeight (d : ℕ) : PolymerWeightFamily d :=
  fun k X => (X.size : ℝ)

/-- Nonnegativity of the size weight family. 0 sorrys. -/
theorem sizeWeight_nonneg (d : ℕ) :
    PolymerWeightFamilyNonneg d (sizeWeight d) := by
  intro k X
  exact_mod_cast Nat.zero_le X.size

/-- Every polymer has size at least `1`, since polymers are nonempty by
definition. 0 sorrys. -/
theorem sizeWeight_ge_one (d : ℕ) :
    PolymerWeightFamilyGeOne d (sizeWeight d) := by
  intro k X
  have hcard : 1 ≤ X.size := by
    exact Finset.one_le_card.mpr X.nonEmpty
  exact_mod_cast hcard

/-! ## Weighted ActivityNorm recovered from size weight -/

section WeightedNorm

variable {d : ℕ}
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- The weighted `ActivityNorm` family induced by the native polymer size.
0 sorrys. -/
instance instActivityNormFromSizeWeight : ∀ j, ActivityNorm d j :=
  instActivityNormFromPolymerWeight
    (d := d) (sizeWeight d) (sizeWeight_nonneg d) (sizeWeight_ge_one d)

end WeightedNorm

/-! ## Native evaluation/Cauchy wrappers -/

section EvaluationWrappers

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Evaluation bound from the native polymer-size weight. 0 sorrys. -/
theorem activityNormEvaluationBoundAt_sizeWeight
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
    ActivityNormEvaluationBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
  exact activityNormEvaluationBoundAt_of_polymerWeight
    (d := d) (N_c := N_c)
    (sizeWeight d) (sizeWeight_nonneg d) (sizeWeight_ge_one d)
    k p₀

/-- Cauchy evaluation bound from the native polymer-size weight. 0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_sizeWeight
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
    ActivityNormEvaluationCauchyBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
  exact activityNormEvaluationCauchyBoundAt_of_polymerWeight
    (d := d) (N_c := N_c)
    (sizeWeight d) (sizeWeight_nonneg d) (sizeWeight_ge_one d)
    k p₀

end EvaluationWrappers

/-! ## Finite full bridge wrappers -/

section FiniteFullWrappers

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Finite full P80 bound from the native polymer-size weight. 0 sorrys. -/
theorem finiteFullLargeFieldBound_sizeWeight
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
    FiniteFullLargeFieldBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
  exact finiteFullLargeFieldBound_of_polymerWeight
    (d := d) (N_c := N_c)
    (sizeWeight d) (sizeWeight_nonneg d) (sizeWeight_ge_one d)
    k β hlargeA polys

/-- Finite full P81 bound from the native polymer-size weight. 0 sorrys. -/
theorem finiteFullCauchyBound_sizeWeight
    (k : ℕ) (β : ℝ)
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
    FiniteFullCauchyBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
  exact finiteFullCauchyBound_of_polymerWeight
    (d := d) (N_c := N_c)
    (sizeWeight d) (sizeWeight_nonneg d) (sizeWeight_ge_one d)
    k β hcauchyA polys

/-- Concrete packaged finite full control from the native polymer-size weight.
0 sorrys. -/
def finiteCanonicalGeometricBridgeControlFull_sizeWeight
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
    RGViaBridgeControlFull d N_c k β := by
  letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
  exact finiteCanonicalGeometricBridgeControlFull_of_polymerWeight
    (d := d) (N_c := N_c)
    (sizeWeight d) (sizeWeight_nonneg d) (sizeWeight_ge_one d)
    k β hlargeA hcauchyA polys

/-- High-level finite full consumer from the native polymer-size weight.
0 sorrys. -/
theorem cauchy_decay_via_finite_full_bridge_control_sizeWeight
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
    let ctrl := finiteCanonicalGeometricBridgeControlFull_sizeWeight
      (d := d) (N_c := N_c) k β hlargeA hcauchyA polys
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) := by
  letI : ∀ j, ActivityNorm d j := instActivityNormFromSizeWeight (d := d)
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end FiniteFullWrappers

end

end YangMills.ClayCore
