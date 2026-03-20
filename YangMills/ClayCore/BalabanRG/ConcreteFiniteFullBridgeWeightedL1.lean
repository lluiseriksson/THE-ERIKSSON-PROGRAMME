import Mathlib
import YangMills.ClayCore.BalabanRG.ConcreteActivityNormWeightedL1
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionFinite
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridgeFiniteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ConcreteFiniteFullBridgeWeightedL1 — (v1.0.12-alpha Phase 2)

Concrete finite-support full-geometry bridge bounds from the weighted finite `L¹`
norm family.

The readout itself is still the unweighted sum
  ∑ p ∈ polys.filter (...), K p
but if the weight satisfies `1 ≤ w p`, then
  |K p| ≤ |K p| * w p,
so the same filtered-subset argument upgrades immediately to the weighted norm.
-/

noncomputable section

section BasicLemmas

variable {d : ℕ} {k : ℕ}
variable [Fintype (Polymer d (Int.ofNat k))]
variable [DecidableEq (Polymer d (Int.ofNat k))]

/-- The weighted `L¹` sum over a filtered finite set is bounded by the global
weighted `L¹` sum provided `1 ≤ w p`. -/
theorem sum_abs_filter_le_weightedL1
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_ge_one : ∀ p, 1 ≤ w p)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (siteOf : Polymer d (Int.ofNat k) → BalabanFiniteSite d k)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    ∑ p ∈ polys.filter (fun p => siteOf p = x), |K p| ≤
      activityWeightedL1Norm (d := d) (k := k) w K := by
  calc
    ∑ p ∈ polys.filter (fun p => siteOf p = x), |K p|
      ≤ ∑ p ∈ polys.filter (fun p => siteOf p = x), |K p| * w p := by
          exact Finset.sum_le_sum (by
            intro p hp
            have hmul := mul_le_mul_of_nonneg_left (hw_ge_one p) (abs_nonneg (K p))
            simpa [one_mul] using hmul)
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Polymer d (Int.ofNat k))), |K p| * w p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
          · intro p hp
            simp at hp
            simp [hp.1]
          · intro p hp hnot
            exact mul_nonneg (abs_nonneg (K p)) (hw_nonneg p)
    _ = activityWeightedL1Norm (d := d) (k := k) w K := by
          simp [activityWeightedL1Norm]

/-- Pointwise full readout bound from the weighted finite `L¹` norm. -/
theorem finiteReadoutFieldFull_abs_le_weightedL1
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_ge_one : ∀ p, 1 ≤ w p)
    (r : FinitePolymerReadoutFull d k)
    (K : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |finiteReadoutFieldFull r K x| ≤ activityWeightedL1Norm (d := d) (k := k) w K := by
  unfold finiteReadoutFieldFull
  calc
    |∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), K p|
      ≤ ∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), |K p| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ activityWeightedL1Norm (d := d) (k := k) w K := by
          exact sum_abs_filter_le_weightedL1
            (d := d) (k := k) w hw_nonneg hw_ge_one r.polys r.siteOf K x

/-- Pointwise full readout Cauchy bound from the weighted finite `L¹` norm. -/
theorem finiteReadoutFieldFull_abs_sub_le_weightedL1
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_ge_one : ∀ p, 1 ≤ w p)
    (r : FinitePolymerReadoutFull d k)
    (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k) :
    |finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x|
      ≤ activityWeightedL1Norm (d := d) (k := k) w (fun p => K₁ p - K₂ p) := by
  have hsum :
      finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x =
        finiteReadoutFieldFull r (fun p => K₁ p - K₂ p) x := by
    unfold finiteReadoutFieldFull
    rw [Finset.sum_sub_distrib]
  calc
    |finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x|
      = |finiteReadoutFieldFull r (fun p => K₁ p - K₂ p) x| := by
          rw [hsum]
    _ ≤ activityWeightedL1Norm (d := d) (k := k) w (fun p => K₁ p - K₂ p) := by
          exact finiteReadoutFieldFull_abs_le_weightedL1
            (d := d) (k := k) w hw_nonneg hw_ge_one r (fun p => K₁ p - K₂ p) x

end BasicLemmas

section FiniteFullWeightedL1

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Finite-support full large-field bound from the weighted finite `L¹` norm
family. 0 sorrys. -/
theorem finiteFullLargeFieldBound_weightedL1
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    FiniteFullLargeFieldBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  intro K x
  calc
    |(canonicalGeometricBridgeFull polys).fieldOfActivity K x|
      = |finiteReadoutFieldFull (canonicalGeometricReadoutFull polys) K x| := by
          rfl
    _ ≤ activityWeightedL1Norm (d := d) (k := k) (w k) K := by
          exact finiteReadoutFieldFull_abs_le_weightedL1
            (d := d) (k := k) (w k) (hw_nonneg k) (hw_ge_one k)
            (canonicalGeometricReadoutFull polys) K x
    _ = ActivityNorm.dist K (fun _ => 0) := by
          rw [ActivityNorm.dist_zero_right]
          rfl
    _ ≤ Real.exp (-β) * ActivityNorm.dist K (fun _ => 0) := by
          have hdist : 0 ≤ ActivityNorm.dist K (fun _ => 0) :=
            ActivityNorm.dist_nonneg K (fun _ => 0)
          have hmul := mul_le_mul_of_nonneg_right hlargeA hdist
          simpa [one_mul] using hmul

/-- Finite-support full Cauchy bound from the weighted finite `L¹` norm family.
0 sorrys. -/
theorem finiteFullCauchyBound_weightedL1
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (β : ℝ)
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    FiniteFullCauchyBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  intro K₁ K₂ x
  calc
    |(canonicalGeometricBridgeFull polys).fieldOfActivity K₁ x -
      (canonicalGeometricBridgeFull polys).fieldOfActivity K₂ x|
      = |finiteReadoutFieldFull (canonicalGeometricReadoutFull polys) K₁ x -
          finiteReadoutFieldFull (canonicalGeometricReadoutFull polys) K₂ x| := by
            rfl
    _ ≤ activityWeightedL1Norm (d := d) (k := k) (w k) (fun p => K₁ p - K₂ p) := by
          exact finiteReadoutFieldFull_abs_sub_le_weightedL1
            (d := d) (k := k) (w k) (hw_nonneg k) (hw_ge_one k)
            (canonicalGeometricReadoutFull polys) K₁ K₂ x
    _ = ActivityNorm.dist K₁ K₂ := by
          rfl
    _ ≤ physicalContractionRate β * ActivityNorm.dist K₁ K₂ := by
          have hdist : 0 ≤ ActivityNorm.dist K₁ K₂ :=
            ActivityNorm.dist_nonneg K₁ K₂
          have hmul := mul_le_mul_of_nonneg_right hcauchyA hdist
          simpa [one_mul] using hmul

/-- Concrete finite-support full bridge control from the weighted finite `L¹`
norm family. 0 sorrys. -/
def finiteCanonicalGeometricBridgeControlFull_weightedL1
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (β : ℝ)
    (hlargeA : (1 : ℝ) ≤ Real.exp (-β))
    (hcauchyA : (1 : ℝ) ≤ physicalContractionRate β)
    (polys : Finset (Polymer d (Int.ofNat k))) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    RGViaBridgeControlFull d N_c k β := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  exact finiteCanonicalGeometricBridgeControlFull
    (d := d) (N_c := N_c) k β polys
    (finiteFullLargeFieldBound_weightedL1
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hlargeA polys)
    (finiteFullCauchyBound_weightedL1
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hcauchyA polys)

end FiniteFullWeightedL1

end

end YangMills.ClayCore
