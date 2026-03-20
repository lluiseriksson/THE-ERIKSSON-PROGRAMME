import Mathlib
import YangMills.ClayCore.BalabanRG.ConcreteActivityNormWeightedL1
import YangMills.ClayCore.BalabanRG.FullLargeFieldSuppressionFinite
import YangMills.ClayCore.BalabanRG.CauchyDecayViaBridgeFiniteFull

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# ConcreteFiniteFullBridgeWeightedL1 — (v1.0.19-alpha)

Concrete finite-support full-geometry bridge bounds from the weighted finite `L¹`
norm family.

This file now contains **two layers**:

1. the legacy coarse layer, which only upgrades the constant `1` to a larger
   target coefficient and therefore requires hypotheses of the form
   `1 ≤ exp(-β)` / `1 ≤ physicalContractionRate β`,
2. the honest small-constants layer, which packages the genuinely missing finite
   full input:
   pointwise readout bounds with explicit constants `A_large`, `A_cauchy`, plus
   refinements `A_large ≤ exp(-β)` and `A_cauchy ≤ physicalContractionRate β`.

The second layer does not fake the missing math. It isolates it explicitly.
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
    (K : ActivityFamily d k)
    (x : BalabanFiniteSite d k) :
    ∑ p ∈ polys.filter (fun p => siteOf p = x), |K p|
      ≤ activityWeightedL1Norm (d := d) (k := k) w K := by
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
    (K : ActivityFamily d k)
    (x : BalabanFiniteSite d k) :
    |finiteReadoutFieldFull r K x|
      ≤ activityWeightedL1Norm (d := d) (k := k) w K := by
  unfold finiteReadoutFieldFull
  calc
    |∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), K p|
        ≤ ∑ p ∈ r.polys.filter (fun p => r.siteOf p = x), |K p| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun p => K p)
              (r.polys.filter (fun p => r.siteOf p = x)))
    _ ≤ activityWeightedL1Norm (d := d) (k := k) w K := by
          exact sum_abs_filter_le_weightedL1
            (d := d) (k := k) w hw_nonneg hw_ge_one r.polys r.siteOf K x

/-- Pointwise full readout Cauchy bound from the weighted finite `L¹` norm. -/
theorem finiteReadoutFieldFull_abs_sub_le_weightedL1
    (w : Polymer d (Int.ofNat k) → ℝ)
    (hw_nonneg : ∀ p, 0 ≤ w p)
    (hw_ge_one : ∀ p, 1 ≤ w p)
    (r : FinitePolymerReadoutFull d k)
    (K₁ K₂ : ActivityFamily d k)
    (x : BalabanFiniteSite d k) :
    |finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x|
      ≤ activityWeightedL1Norm (d := d) (k := k) w (fun p => K₁ p - K₂ p) := by
  have hsum :
      finiteReadoutFieldFull r K₁ x - finiteReadoutFieldFull r K₂ x
        = finiteReadoutFieldFull r (fun p => K₁ p - K₂ p) x := by
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
family. Legacy coarse version. -/
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
Legacy coarse version. -/
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
norm family. Legacy coarse version. -/
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
  exact finiteCanonicalGeometricBridgeControlFull (d := d) (N_c := N_c) k β polys
    (finiteFullLargeFieldBound_weightedL1
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hlargeA polys)
    (finiteFullCauchyBound_weightedL1
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β hcauchyA polys)

end FiniteFullWeightedL1

section FiniteFullWeightedL1SmallConstants

variable {d N_c : ℕ} [NeZero N_c]
variable [∀ j, Fintype (Polymer d (Int.ofNat j))]
variable [∀ j, DecidableEq (Polymer d (Int.ofNat j))]

/-- Honest finite-support full large-field upgrade:
if one already has a pointwise constant `A_large`, and this constant refines to
`exp(-β)`, then one gets the standard finite-full P80 bound. -/
theorem finiteFullLargeFieldBound_weightedL1_of_constants
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (β : ℝ)
    (A_large : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (hlarge :
      letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
        (d := d) w hw_nonneg hw_ge_one
      ∀ (K : ActivityFamily d k) (x : BalabanFiniteSite d k),
        |(canonicalGeometricBridgeFull polys).fieldOfActivity K x|
          ≤ A_large * ActivityNorm.dist K (fun _ => 0))
    (hlargeA : A_large ≤ Real.exp (-β)) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    FiniteFullLargeFieldBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  intro K x
  exact le_trans (hlarge K x)
    (mul_le_mul_of_nonneg_right hlargeA
      (ActivityNorm.dist_nonneg K (fun _ => 0)))

/-- Honest finite-support full Cauchy upgrade:
if one already has a pointwise constant `A_cauchy`, and this constant refines to
`physicalContractionRate β`, then one gets the standard finite-full P81 bound. -/
theorem finiteFullCauchyBound_weightedL1_of_constants
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (β : ℝ)
    (A_cauchy : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (hcauchy :
      letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
        (d := d) w hw_nonneg hw_ge_one
      ∀ (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k),
        |(canonicalGeometricBridgeFull polys).fieldOfActivity K₁ x -
          (canonicalGeometricBridgeFull polys).fieldOfActivity K₂ x|
          ≤ A_cauchy * ActivityNorm.dist K₁ K₂)
    (hcauchyA : A_cauchy ≤ physicalContractionRate β) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    FiniteFullCauchyBound d N_c k β polys := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  intro K₁ K₂ x
  exact le_trans (hcauchy K₁ K₂ x)
    (mul_le_mul_of_nonneg_right hcauchyA
      (ActivityNorm.dist_nonneg K₁ K₂))

/-- Honest packaged finite-support full bridge control from weighted `L¹`
small constants. -/
def finiteCanonicalGeometricBridgeControlFull_weightedL1_of_constants
    (w : ∀ j, Polymer d (Int.ofNat j) → ℝ)
    (hw_nonneg : ∀ j p, 0 ≤ w j p)
    (hw_ge_one : ∀ j p, 1 ≤ w j p)
    (k : ℕ) (β : ℝ)
    (A_large A_cauchy : ℝ)
    (polys : Finset (Polymer d (Int.ofNat k)))
    (hlarge :
      letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
        (d := d) w hw_nonneg hw_ge_one
      ∀ (K : ActivityFamily d k) (x : BalabanFiniteSite d k),
        |(canonicalGeometricBridgeFull polys).fieldOfActivity K x|
          ≤ A_large * ActivityNorm.dist K (fun _ => 0))
    (hlargeA : A_large ≤ Real.exp (-β))
    (hcauchy :
      letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
        (d := d) w hw_nonneg hw_ge_one
      ∀ (K₁ K₂ : ActivityFamily d k) (x : BalabanFiniteSite d k),
        |(canonicalGeometricBridgeFull polys).fieldOfActivity K₁ x -
          (canonicalGeometricBridgeFull polys).fieldOfActivity K₂ x|
          ≤ A_cauchy * ActivityNorm.dist K₁ K₂)
    (hcauchyA : A_cauchy ≤ physicalContractionRate β) :
    letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
      (d := d) w hw_nonneg hw_ge_one
    RGViaBridgeControlFull d N_c k β := by
  letI : ∀ j, ActivityNorm d j := instActivityNormWeightedL1All
    (d := d) w hw_nonneg hw_ge_one
  exact finiteCanonicalGeometricBridgeControlFull (d := d) (N_c := N_c) k β polys
    (finiteFullLargeFieldBound_weightedL1_of_constants
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β A_large polys hlarge hlargeA)
    (finiteFullCauchyBound_weightedL1_of_constants
      (d := d) (N_c := N_c) w hw_nonneg hw_ge_one k β A_cauchy polys hcauchy hcauchyA)

end FiniteFullWeightedL1SmallConstants

end

end YangMills.ClayCore
