/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixSparseWalk
import YangMills.RG.BalabanCMP99PatchedParametrixAnchoredSparseWalk
import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrix
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm

/-!
# Exact all-head source `Pi^4` sparse-walk matrix

The source contour estimates are naturally organized one anchored head at a
time.  The inverse of the physical precision is not one such anchored series:
it contains every source-cell head.  This file records the exact all-head
object, still ordered by walk length as in the defect Neumann series.

The terminal theorem says that the physical precision matrix times the matrix
of the complete sparse-walk series is the identity.  No single-head series is
identified with the covariance, and no matrix inverse hypothesis is supplied.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The exact length-`n` layer: sum over every literal source-cell head and
every physically admissible continuation word. -/
noncomputable def cmp116SourcePi4ExactSparseWalkLayer
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (R n : ℕ) :
    PhysicalEndomorphism M Q Nc :=
  ∑ head : ↥(Finset.univ : Finset (FinBox 4 Q)),
    ∑ word ∈ cmp99PhysicalPatchAdmissibleWords
        (Finset.univ : Finset (FinBox 4 Q))
        (cmp99SourceBaseCellBondCore (M := M))
        (cmp99SourcePi4PhysicalBondSupport (M := M))
        physicalBondDist R n,
      (cmp99SingleSpeciesWalk head word).term
        (cmp99PhysicalPatchHead
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)

/-- The same source layer, now indexed only by continuation words whose first
step is physically admissible from the distinguished head. -/
noncomputable def cmp116SourcePi4ExactHeadAnchoredWalkLayer
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (R n : ℕ) :
    PhysicalEndomorphism M Q Nc :=
  ∑ head : ↥(Finset.univ : Finset (FinBox 4 Q)),
    ∑ word ∈ cmp99PhysicalPatchHeadAnchoredAdmissibleWords
        (Finset.univ : Finset (FinBox 4 Q))
        (cmp99SourceBaseCellBondCore (M := M))
        (cmp99SourcePi4PhysicalBondSupport (M := M))
        physicalBondDist R head n,
      (cmp99SingleSpeciesWalk head word).term
        (cmp99PhysicalPatchHead
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)

/-- The exact source layer written in the pre-existing certified
`CMP99AnchoredWalk` tail representation. -/
noncomputable def cmp116SourcePi4ExactGeneratedAnchoredWalkLayer
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (R n : ℕ) :
    PhysicalEndomorphism M Q Nc :=
  ∑ head : ↥(Finset.univ : Finset (FinBox 4 Q)),
    ∑ tail : ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (Finset.univ : Finset (FinBox 4 Q))
          (cmp99SourceBaseCellBondCore (M := M))
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          physicalBondDist R)
        head n),
      (CMP99AnchoredWalk.toGeneralizedWalk
        (⟨n, tail⟩ : CMP99AnchoredWalk
          (cmp99PhysicalPatchSuccessorSteps
            (Finset.univ : Finset (FinBox 4 Q))
            (cmp99SourceBaseCellBondCore (M := M))
            (cmp99SourcePi4PhysicalBondSupport (M := M))
            physicalBondDist R)
          head)).term
        (cmp99PhysicalPatchHead
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)

/-- The finite head-anchored word layer is exactly the generated-tail layer. -/
theorem cmp116SourcePi4ExactHeadAnchoredWalkLayer_eq_generated
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (R n : ℕ) :
    cmp116SourcePi4ExactHeadAnchoredWalkLayer K hc hmass hK R n =
      cmp116SourcePi4ExactGeneratedAnchoredWalkLayer
        K hc hmass hK R n := by
  classical
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [← Finset.sum_coe_sort]
  let e := cmp99PhysicalPatchHeadAnchoredWordsEquivTails
    (Finset.univ : Finset (FinBox 4 Q))
    (cmp99SourceBaseCellBondCore (M := M))
    (cmp99SourcePi4PhysicalBondSupport (M := M))
    physicalBondDist R head n
  let f :
      ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (Finset.univ : Finset (FinBox 4 Q))
          (cmp99SourceBaseCellBondCore (M := M))
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          physicalBondDist R)
        head n) →
      PhysicalEndomorphism M Q Nc := fun tail =>
    (CMP99AnchoredWalk.toGeneralizedWalk
      (⟨n, tail⟩ : CMP99AnchoredWalk
        (cmp99PhysicalPatchSuccessorSteps
          (Finset.univ : Finset (FinBox 4 Q))
          (cmp99SourceBaseCellBondCore (M := M))
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          physicalBondDist R)
        head)).term
      (cmp99PhysicalPatchHead
        (Finset.univ : Finset (FinBox 4 Q))
        K
        (cmp99SourcePi4PhysicalBondSupport (M := M))
        (cmp99SourceBaseCellBondCore (M := M))
        hc hmass hK)
      (fun _ => cmp99PhysicalPatchContinuation
        (Finset.univ : Finset (FinBox 4 Q))
        K
        (cmp99SourcePi4PhysicalBondSupport (M := M))
        (cmp99SourceBaseCellBondCore (M := M))
        hc hmass hK)
  calc
    (∑ word :
        ↥(cmp99PhysicalPatchHeadAnchoredAdmissibleWords
          (Finset.univ : Finset (FinBox 4 Q))
          (cmp99SourceBaseCellBondCore (M := M))
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          physicalBondDist R head n),
      (cmp99SingleSpeciesWalk head word.1).term
        (cmp99PhysicalPatchHead
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK)) =
        ∑ word, f (e word) := by
          apply Finset.sum_congr rfl
          intro word _hword
          rfl
    _ = ∑ tail, f tail := e.sum_comp f

/-- Exact equality between the continuation-only sparse layer and its
head-anchored refinement. -/
theorem cmp116SourcePi4ExactSparseWalkLayer_eq_headAnchored
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    cmp116SourcePi4ExactSparseWalkLayer K hc hmass hK R n =
      cmp116SourcePi4ExactHeadAnchoredWalkLayer K hc hmass hK R n := by
  classical
  have hsub : ∀ cell : FinBox 4 Q,
      cell ∈ (Finset.univ : Finset (FinBox 4 Q)) →
      cmp99SourceBaseCellBondCore (M := M) cell ⊆
        cmp99SourcePi4PhysicalBondSupport cell := by
    intro cell _hcell
    exact cmp99SourceBaseCellBondCore_subset_pi4PhysicalSupport
      (M := M) (Q := Q) cell hsourceRange
  apply Finset.sum_congr rfl
  intro head _hhead
  exact sum_cmp99PhysicalPatchAdmissibleWords_eq_headAnchored
    (Finset.univ : Finset (FinBox 4 Q))
    K
    (cmp99SourcePi4PhysicalBondSupport (M := M))
    (cmp99SourceBaseCellBondCore (M := M))
    hsub physicalBondDist hrange hc hmass hK head n

/-- The complete corrected covariance is literally the length-ordered sum of
all source heads and all physically surviving continuation words. -/
theorem cmp116SourcePi4ExactPatchedCovariance_eq_tsum_sparseWalkLayers
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4ExactPatchedCovariance K hc hmass hK =
      ∑' n : ℕ,
        cmp116SourcePi4ExactSparseWalkLayer K hc hmass hK R n := by
  have hsub : ∀ cell : FinBox 4 Q,
      cell ∈ (Finset.univ : Finset (FinBox 4 Q)) →
      cmp99SourceBaseCellBondCore (M := M) cell ⊆
        cmp99SourcePi4PhysicalBondSupport cell := by
    intro cell _hcell
    exact cmp99SourceBaseCellBondCore_subset_pi4PhysicalSupport
      (M := M) (Q := Q) cell hsourceRange
  simpa [cmp116SourcePi4ExactPatchedCovariance,
    cmp116SourcePi4ExactSparseWalkLayer] using
    (cmp99CorrectedPatchedPhysicalCovariance_eq_tsum_sparse_walk_layers
      (Finset.univ : Finset (FinBox 4 Q))
      K
      (cmp99SourcePi4PhysicalBondSupport (M := M))
      (cmp99SourceBaseCellBondCore (M := M))
      hsub physicalBondDist
      hrange hc hmass hK hD)

/-- Exact covariance expansion with the head transition included in every
finite walk index. -/
theorem cmp116SourcePi4ExactPatchedCovariance_eq_tsum_headAnchoredWalkLayers
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4ExactPatchedCovariance K hc hmass hK =
      ∑' n : ℕ,
        cmp116SourcePi4ExactHeadAnchoredWalkLayer
          K hc hmass hK R n := by
  rw [cmp116SourcePi4ExactPatchedCovariance_eq_tsum_sparseWalkLayers
    K hsourceRange hrange hc hmass hK hD]
  apply tsum_congr
  intro n
  exact cmp116SourcePi4ExactSparseWalkLayer_eq_headAnchored
    K hsourceRange hrange hc hmass hK n

/-- Exact all-head covariance written with the same `CMP99AnchoredWalk`
fibers consumed by the source-specific walk estimates. -/
theorem cmp116SourcePi4ExactPatchedCovariance_eq_tsum_generatedAnchoredWalkLayers
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4ExactPatchedCovariance K hc hmass hK =
      ∑' n : ℕ,
        cmp116SourcePi4ExactGeneratedAnchoredWalkLayer
          K hc hmass hK R n := by
  rw [
    cmp116SourcePi4ExactPatchedCovariance_eq_tsum_headAnchoredWalkLayers
      K hsourceRange hrange hc hmass hK hD]
  apply tsum_congr
  intro n
  exact cmp116SourcePi4ExactHeadAnchoredWalkLayer_eq_generated
    K hc hmass hK R n

/-- Matrix form of the complete all-head sparse-walk inverse.  The matrix
contains the length-ordered physical series, rather than a fixed-head
contour contribution. -/
theorem cmp116SourcePi4_precision_mul_tsum_sparseWalkLayerMatrix_eq_one
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116PhysicalEndomorphismComplexMatrix
          (∑' n : ℕ,
            cmp116SourcePi4ExactSparseWalkLayer
              K hc hmass hK R n) =
      1 := by
  rw [← cmp116SourcePi4ExactPatchedCovariance_eq_tsum_sparseWalkLayers
    K hsourceRange hrange hc hmass hK hD]
  exact cmp116SourcePi4_precision_mul_exactCovarianceMatrix_eq_one
    K hc hmass hK hD

/-- Matrix inverse identity for the genuinely head-anchored source expansion. -/
theorem cmp116SourcePi4_precision_mul_tsum_headAnchoredWalkLayerMatrix_eq_one
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116PhysicalEndomorphismComplexMatrix
          (∑' n : ℕ,
            cmp116SourcePi4ExactHeadAnchoredWalkLayer
              K hc hmass hK R n) =
      1 := by
  rw [←
    cmp116SourcePi4ExactPatchedCovariance_eq_tsum_headAnchoredWalkLayers
      K hsourceRange hrange hc hmass hK hD]
  exact cmp116SourcePi4_precision_mul_exactCovarianceMatrix_eq_one
    K hc hmass hK hD

/-- Matrix inverse identity in the generated `CMP99AnchoredWalk`
representation used by the analytic source bounds. -/
theorem cmp116SourcePi4_precision_mul_tsum_generatedAnchoredWalkLayerMatrix_eq_one
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116PhysicalEndomorphismComplexMatrix
          (∑' n : ℕ,
            cmp116SourcePi4ExactGeneratedAnchoredWalkLayer
              K hc hmass hK R n) =
      1 := by
  rw [←
    cmp116SourcePi4ExactPatchedCovariance_eq_tsum_generatedAnchoredWalkLayers
      K hsourceRange hrange hc hmass hK hD]
  exact cmp116SourcePi4_precision_mul_exactCovarianceMatrix_eq_one
    K hc hmass hK hD

/-- Named all-head generated-walk covariance matrix. -/
noncomputable def cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (R : ℕ) :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (∑' n : ℕ,
      cmp116SourcePi4ExactGeneratedAnchoredWalkLayer
        K hc hmass hK R n)

/-- The named generated-walk matrix is exactly the canonical matrix of the
complete corrected covariance. -/
theorem cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix_eq_exact
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix
        K hc hmass hK R =
      cmp116PhysicalEndomorphismComplexMatrix
        (cmp116SourcePi4ExactPatchedCovariance K hc hmass hK) := by
  rw [cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix,
    ←
      cmp116SourcePi4ExactPatchedCovariance_eq_tsum_generatedAnchoredWalkLayers
        K hsourceRange hrange hc hmass hK hD]

/-- The physical precision matrix is nonsingular, derived from the exact
all-head walk covariance rather than postulated. -/
theorem det_cmp116SourcePi4PhysicalPrecisionMatrix_ne_zero
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    (cmp116PhysicalEndomorphismComplexMatrix K).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_mul_eq_one
    (cmp116PhysicalEndomorphismComplexMatrix K)
    (cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix
      K hc hmass hK R)
    (by
      simpa [cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix] using
        cmp116SourcePi4_precision_mul_tsum_generatedAnchoredWalkLayerMatrix_eq_one
          K hsourceRange hrange hc hmass hK hD)

/-- The complete generated-walk covariance matrix is likewise nonsingular. -/
theorem det_cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix_ne_zero
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (Finset.univ : Finset (FinBox 4 Q))
          K
          (cmp99SourcePi4PhysicalBondSupport (M := M))
          (cmp99SourceBaseCellBondCore (M := M))
          hc hmass hK‖ < 1) :
    (cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix
      K hc hmass hK R).det ≠ 0 := by
  have hmul :
      cmp116PhysicalEndomorphismComplexMatrix K *
          cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix
            K hc hmass hK R = 1 := by
    simpa [cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix] using
      cmp116SourcePi4_precision_mul_tsum_generatedAnchoredWalkLayerMatrix_eq_one
        K hsourceRange hrange hc hmass hK hD
  exact Matrix.det_ne_zero_of_mul_eq_one
    (cmp116SourcePi4ExactGeneratedAnchoredCovarianceMatrix
      K hc hmass hK R)
    (cmp116PhysicalEndomorphismComplexMatrix K)
    (mul_eq_one_comm.mp hmul)

end

end YangMills.RG
