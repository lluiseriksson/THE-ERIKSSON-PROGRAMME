import Mathlib
import YangMills.ClayCore.BalabanRG.ConcreteActivityNormL1
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionFinite
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridgeFiniteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ConcreteFiniteFullBridgeL1 — (v1.0.11-alpha Phase 1)

Concrete finite-support full-geometry bridge bounds from the finite `L¹` norm.

This extends the discharged singleton `L¹` path to arbitrary finite support
`polys : Finset (Polymer ...)` in the full canonical bridge.

Key observation:
for each site `x`, the full readout is a sum over a filtered subset of `polys`,
so its absolute value is bounded by the `L¹` norm of `K`, hence by
`ActivityNorm.dist K 0` for the concrete `L¹` family.

Likewise, the Cauchy estimate follows by applying the same argument to `K₁ - K₂`.
-/

noncomputable section

section BasicLemmas

variable {d : ℕ} {k : ℕ}
variable [Fintype (Polymer d (Int.ofNat k))]
variable [DecidableEq (Polymer d (Int.ofNat k))]

/-- The `L¹` sum over a filtered finite set is bounded by the global `L¹` sum. -/
theorem sum_abs_filter_le_l1
    (polys : Finset (Polymer d (Int.ofNat k)))
    (siteOf : Polymer d (Int.ofNat k) → BalabanFiniteSite d k)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    ∑ p ∈ polys.filter (fun p => siteOf p = x), |K p| ≤
      activityL1Norm (d := d) (k := k) K := by
  calc
    ∑ p ∈ polys.filter (fun p => siteOf p = x), |K p|
      ≤ ∑ p ∈ (Finset.univ : Finset (Polymer d (Int.ofNat k))), |K p| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
        · intro p hp
          simp at hp
          simp [hp.1]
        · intro p hp hnot
          exact abs_nonneg (K p)
    _ = activityL1Norm (d := d) (k := k) K := by
        simp [activityL1Norm]

/-- Pointwise full readout bound from the concrete `L¹` norm. -/
theorem finiteReadoutFieldFull_abs_le_l1
    (r : FinitePolymerReadoutFull d k)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |finiteReadoutFieldFull r K x| ≤ activityL1Norm (d := d) (k := k) K := by
  unfold finiteReadoutFieldFull
  calc
    |∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), K p|
      ≤ ∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), |K p| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ activityL1Norm (d := d) (k := k) K := by
          exact sum_abs_filter_le_l1 (d := d) (k := k) r.polys r.siteOf K x

/-- Pointwise full readout Cauchy bound from the concrete `L¹` norm. -/
theorem finiteReadoutFieldFull_abs_sub_le_l1
    (r : FinitePolymerReadoutFull d k)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x|
      ≤ activityL1Norm (d := d) (k := k) (fun p => K₁ p - K₂ p) := by
  have hsum :
      finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x =
        finiteReadoutFieldFull r (fun p => K₁ p - K₂ p) x := by
    unfold finiteReadoutFieldFull
    rw [Finset.sum_sub_distrib]
  calc
    |finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x|
      = |finiteReadoutFieldFull r (fun p => K₁ p - K₂ p) x| := by
          rw [hsum]
    _ ≤ activityL1Norm (d := d) (k := k) (fun p => K₁ p - K₂ p) := by
          exact finiteReadoutFieldFull_abs_le_l1 (d := d) (k := k) r (fun p => K₁ p - K₂ p) x

end BasicLemmas

section FiniteFullL1

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Finite-support full large-field bound from the concrete `L¹` norm family.
0 sorrys. -/
theorem finiteFullLargeFieldBound_l1
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
    FiniteFullLargeFieldBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
  intro K x
  calc
    |(canonicalGeometricBridgeFull polys).fieldOfActivity K x|
      = |finiteReadoutFieldFull (canonicalGeometricReadoutFull polys) K x| := by
          rfl
    _ ≤ activityL1Norm (d := d) (k := k) K := by
          exact finiteReadoutFieldFull_abs_le_l1
            (d := d) (k := k) (canonicalGeometricReadoutFull polys) K x
    _ = ActivityNorm.dist K (fun _ => 0) := by
          rw [ActivityNorm.dist_zero_right]
          rfl
    _ ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) := by
          have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) :=
            ActivityNorm.dist_nonneg K (fun _ => 0)
          have hmul := mul_le_mul_of_nonneg_right hlargeA hdist
          simpa using hmul

/-- Finite-support full Cauchy bound from the concrete `L¹` norm family.
0 sorrys. -/
theorem finiteFullCauchyBound_l1
    (k : ℕ) (β : ℝ)
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
    FiniteFullCauchyBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
  intro K₁ K₂ x
  calc
    |(canonicalGeometricBridgeFull polys).fieldOfActivity K₁ x -
      (canonicalGeometricBridgeFull polys).fieldOfActivity K₂ x|
      = |finiteReadoutFieldFull (canonicalGeometricReadoutFull polys) K₁ x -
          finiteReadoutFieldFull (canonicalGeometricReadoutFull polys) K₂ x| := by
            rfl
    _ ≤ activityL1Norm (d := d) (k := k) (fun p => K₁ p - K₂ p) := by
          exact finiteReadoutFieldFull_abs_sub_le_l1
            (d := d) (k := k) (canonicalGeometricReadoutFull polys) K₁ K₂ x
    _ = ActivityNorm.dist K₁ K₂ := by
          rfl
    _ ≤ physicalContractionRate β * ActivityNorm.dist K₁ K₂ := by
          have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ :=
            ActivityNorm.dist_nonneg K₁ K₂
          have hmul := mul_le_mul_of_nonneg_right hcauchyA hdist
          simpa [one_mul] using hmul

/-- Concrete finite-support full bridge control from the `L¹` norm family.
0 sorrys. -/
def finiteCanonicalGeometricBridgeControlFull_l1
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
    RGViaBridgeControlFull d N_c k β := by
  letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
  exact finiteCanonicalGeometricBridgeControlFull
    (d := d) (N_c := N_c) k β polys
    (finiteFullLargeFieldBound_l1 (d := d) (N_c := N_c) k β hlargeA polys)
    (finiteFullCauchyBound_l1 (d := d) (N_c := N_c) k β hcauchyA polys)

/-- High-level finite-support full bridge consumer from the concrete `L¹` norm
family. 0 sorrys. -/
theorem cauchy_decay_via_finite_full_bridge_control_l1
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
    let ctrl := finiteCanonicalGeometricBridgeControlFull_l1
      (d := d) (N_c := N_c) k β hlargeA hcauchyA polys
    (|ctrl.core.bridge.fieldOfActivity K₁ x| ≤
      Real.exp (-β) * ActivityNorm.dist K₁ (fun _ => 0)) ∧
    (|ctrl.core.bridge.fieldOfActivity K₁ x -
      ctrl.core.bridge.fieldOfActivity K₂ x| ≤
      physicalContractionRate β * ActivityNorm.dist K₁ K₂) := by
  letI : ∀ j, ActivityNorm d j := instActivityNormL1All (d := d)
  intro ctrl
  exact cauchy_decay_via_finite_full_bridge_control ctrl K₁ K₂ x

end FiniteFullL1

end

end YangMills.ClayCore
