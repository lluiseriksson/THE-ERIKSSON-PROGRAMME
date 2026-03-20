import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerSizeWeight

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ExpPolymerSizeWeight — (v1.0.14-alpha Phase 1)

First KP-shaped concrete polymer weight built from the native size:

  w_a(X) = exp(a * |X|)

where `|X| = Polymer.size X = X.sites.card`.

This phase is deliberately conservative:
- define the exponential size weight family,
- prove the minimal interface facts `0 ≤ w` and `1 ≤ w` for `a ≥ 0`,
- instantiate the weighted `ActivityNorm` family through the abstract interface,
- recover the existing evaluation / finite-full bridge wrappers through that interface.

This does not yet modify the high-level API file.
-/

noncomputable section

/-! ## Concrete exponential size weight -/

/-- Exponential size weight family:
`w_a(X) = exp(a * |X|)`. -/
abbrev expSizeWeight (a : ℝ) (d : ℕ) : PolymerWeightFamily d :=
  fun k X => Real.exp (a * (X.size : ℝ))

/-- Nonnegativity of the exponential size weight family. 0 sorrys. -/
theorem expSizeWeight_nonneg (a : ℝ) (d : ℕ) :
    PolymerWeightFamilyNonneg d (expSizeWeight a d) := by
  intro k X
  exact le_of_lt (Real.exp_pos _)

/-- For `a ≥ 0`, the exponential size weight satisfies `1 ≤ w_a(X)`.
0 sorrys. -/
theorem expSizeWeight_ge_one {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    PolymerWeightFamilyGeOne d (expSizeWeight a d) := by
  intro k X
  have hsize : 0 ≤ (X.size : ℝ) := by
    exact_mod_cast Nat.zero_le X.size
  have hmul : 0 ≤ a * (X.size : ℝ) := mul_nonneg ha hsize
  have hExp : a * (X.size : ℝ) + 1 ≤ Real.exp (a * (X.size : ℝ)) := by
    simpa using (Real.add_one_le_exp (a * (X.size : ℝ)))
  linarith

/-! ## Weighted ActivityNorm recovered from exponential size weight -/

section WeightedNorm

variable {d : ℕ}
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- The weighted `ActivityNorm` family induced by `w_a(X)=exp(a|X|)`.
0 sorrys. -/
instance instActivityNormFromExpSizeWeight
    (a : ℝ) (ha : 0 ≤ a) : ∀ j, ActivityNorm d j :=
  instActivityNormFromPolymerWeight
    (d := d) (expSizeWeight a d)
    (expSizeWeight_nonneg a d)
    (expSizeWeight_ge_one ha d)

end WeightedNorm

/-! ## Native evaluation/Cauchy wrappers -/

section EvaluationWrappers

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Evaluation bound from the exponential size weight family. 0 sorrys. -/
theorem activityNormEvaluationBoundAt_expSizeWeight
    (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    ActivityNormEvaluationBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) a ha
  exact activityNormEvaluationBoundAt_of_polymerWeight
    (d := d) (N_c := N_c)
    (expSizeWeight a d)
    (expSizeWeight_nonneg a d)
    (expSizeWeight_ge_one ha d)
    k p₀

/-- Cauchy evaluation bound from the exponential size weight family.
0 sorrys. -/
theorem activityNormEvaluationCauchyBoundAt_expSizeWeight
    (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (p₀ : Polymer d (Int.ofNat k)) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    ActivityNormEvaluationCauchyBoundAt d N_c k 1 p₀ := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) a ha
  exact activityNormEvaluationCauchyBoundAt_of_polymerWeight
    (d := d) (N_c := N_c)
    (expSizeWeight a d)
    (expSizeWeight_nonneg a d)
    (expSizeWeight_ge_one ha d)
    k p₀

end EvaluationWrappers

/-! ## Finite full bridge wrappers -/

section FiniteFullWrappers

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Finite full P80 bound from the exponential size weight family. 0 sorrys. -/
theorem finiteFullLargeFieldBound_expSizeWeight
    (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    FiniteFullLargeFieldBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) a ha
  exact finiteFullLargeFieldBound_of_polymerWeight
    (d := d) (N_c := N_c)
    (expSizeWeight a d)
    (expSizeWeight_nonneg a d)
    (expSizeWeight_ge_one ha d)
    k β hlargeA polys

/-- Finite full P81 bound from the exponential size weight family. 0 sorrys. -/
theorem finiteFullCauchyBound_expSizeWeight
    (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (β : ℝ)
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    FiniteFullCauchyBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) a ha
  exact finiteFullCauchyBound_of_polymerWeight
    (d := d) (N_c := N_c)
    (expSizeWeight a d)
    (expSizeWeight_nonneg a d)
    (expSizeWeight_ge_one ha d)
    k β hcauchyA polys

/-- Concrete packaged finite full control from the exponential size weight
family. 0 sorrys. -/
def finiteCanonicalGeometricBridgeControlFull_expSizeWeight
    (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    RGViaBridgeControlFull d N_c k β := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) a ha
  exact finiteCanonicalGeometricBridgeControlFull_of_polymerWeight
    (d := d) (N_c := N_c)
    (expSizeWeight a d)
    (expSizeWeight_nonneg a d)
    (expSizeWeight_ge_one ha d)
    k β hlargeA hcauchyA polys

/-- High-level finite full consumer from the exponential size weight family.
0 sorrys. -/
theorem cauchy_decay_via_finite_full_bridge_control_expSizeWeight
    (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    letI : ∀ j, ActivityNorm d j :=
      instActivityNormFromExpSizeWeight (d := d) a ha
    let ctrl := finiteCanonicalGeometricBridgeControlFull_expSizeWeight
      (d := d) (N_c := N_c) a ha k β hlargeA hcauchyA polys
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) := by
  letI : ∀ j, ActivityNorm d j :=
    instActivityNormFromExpSizeWeight (d := d) a ha
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end FiniteFullWrappers

end

end YangMills.ClayCore
