/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4QuotientExactCovariance
import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier
import YangMills.RG.BalabanCMP99PatchedParametrixAnchoredSparseWalk

/-!
# Complete source `Pi^4` weakened covariance

The source complex estimates were originally exposed one head at a time.
This file defines the physical covariance as a length-ordered sum over every
quotient-safe source head and every generated admissible tail.  Weakening is
inserted by the literal `sigma_0` active carrier.

At the fully coupled point `s = 1`, the monomial disappears and the complete
series is proved equal to the exact corrected covariance.  Thus this is a
global covariance, not a single-head contribution.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The length-`n` all-head quotient-safe generated-walk layer. -/
noncomputable def cmp116SourcePi4QuotientGeneratedWalkLayer
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    PhysicalEndomorphism M Q Nc :=
  ∑ head : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)),
    ∑ tail : ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged
          physicalBondDist R)
        head n),
      (CMP99AnchoredWalk.toGeneralizedWalk
        (⟨n, tail⟩ : CMP99AnchoredWalk
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged
            physicalBondDist R)
          head)).term
        (cmp99PhysicalPatchHead
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK)

/-- Each generated quotient layer is literally the corresponding
patched-parametrix defect power. -/
theorem cmp99SourcePi4_patchedParametrix_mul_neg_defect_pow_eq_generatedLayer
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    cmp99PatchedPhysicalParametrix
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK *
        (-cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK) ^ n =
      cmp116SourcePi4QuotientGeneratedWalkLayer
        (R := R) K hc hmass hK n := by
  have hsub : ∀ chart : CMP99SourcePi4Chart Unit Q,
      chart ∈ (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) →
      cmp99SourcePi4ChartCore (M := M) chart ⊆
        cmp99SourcePi4ChartEnlarged chart := by
    intro chart _hchart
    exact cmp99SourcePi4ChartCore_subset_enlarged hsourceRange chart
  rw [
    cmp99PatchedPhysicalParametrix_mul_neg_defect_pow_eq_sparse_walk_sum
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hsub physicalBondDist hrange hc hmass hK]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [sum_cmp99PhysicalPatchAdmissibleWords_eq_headAnchored
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hsub physicalBondDist hrange hc hmass hK head n]
  exact
    sum_cmp99PhysicalPatchHeadAnchoredWords_eq_admissibleTails
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      physicalBondDist R hc hmass hK head n

/-- Defect contraction makes the complete family of generated quotient
layers summable in the physical operator norm. -/
theorem summable_cmp116SourcePi4QuotientGeneratedWalkLayer
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    Summable fun n : ℕ =>
      cmp116SourcePi4QuotientGeneratedWalkLayer
        (R := R) K hc hmass hK n := by
  have hsum :=
    (summable_cmp99PatchedDefectNeumannInverse hD).mul_left
      (cmp99PatchedPhysicalParametrix
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M))
        hc hmass hK)
  exact hsum.congr fun n =>
    cmp99SourcePi4_patchedParametrix_mul_neg_defect_pow_eq_generatedLayer
      K hsourceRange hrange hc hmass hK n

/-- Exact covariance as the length-ordered generated walk series on the same
quotient charts used by the weakening construction. -/
theorem cmp116SourcePi4QuotientExactPatchedCovariance_eq_tsum_generatedLayers
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4QuotientExactPatchedCovariance K hc hmass hK =
      ∑' n : ℕ,
        cmp116SourcePi4QuotientGeneratedWalkLayer
          (R := R) K hc hmass hK n := by
  have hsub : ∀ chart : CMP99SourcePi4Chart Unit Q,
      chart ∈ (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) →
      cmp99SourcePi4ChartCore (M := M) chart ⊆
        cmp99SourcePi4ChartEnlarged chart := by
    intro chart _hchart
    exact cmp99SourcePi4ChartCore_subset_enlarged hsourceRange chart
  rw [cmp116SourcePi4QuotientExactPatchedCovariance,
    cmp99CorrectedPatchedPhysicalCovariance_eq_tsum_sparse_walk_layers
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hsub physicalBondDist hrange hc hmass hK hD]
  apply tsum_congr
  intro n
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [sum_cmp99PhysicalPatchAdmissibleWords_eq_headAnchored
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hsub physicalBondDist hrange hc hmass hK head n]
  exact
    sum_cmp99PhysicalPatchHeadAnchoredWords_eq_admissibleTails
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      physicalBondDist R hc hmass hK head n

/-- The literal source `sigma_0` active carrier of a generated quotient walk. -/
noncomputable def cmp116SourcePi4QuotientWalkActive
    {M Q R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (walk : CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R)
      head) :
    Finset (FinBox 4 (2 * Q)) :=
  walk.active fun chart =>
    cmp99SourceDomainLargeBlocks chart.1.domain ∩
      cmp116SourceSigmaZero anchor

/-- Length-`n` all-head covariance layer with literal weakening monomials. -/
noncomputable def cmp116SourcePi4FullWeakenedCovarianceLayer
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ) (n : ℕ) :
    PhysicalEndomorphism M Q Nc :=
  ∑ head : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)),
    ∑ tail : ↥(cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged
          physicalBondDist R)
        head n),
      let walk : CMP99AnchoredWalk
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged
            physicalBondDist R)
          head := ⟨n, tail⟩
      cmp116WeakeningMonomial
          (cmp116SourcePi4QuotientWalkActive
            (M := M) anchor head walk) s •
        walk.term
          (cmp99PhysicalPatchHead
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            K cmp99SourcePi4ChartEnlarged
            (cmp99SourcePi4ChartCore (M := M))
            hc hmass hK)
          (fun _ => cmp99PhysicalPatchContinuation
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            K cmp99SourcePi4ChartEnlarged
            (cmp99SourcePi4ChartCore (M := M))
            hc hmass hK)

/-- Complete length-ordered weakened physical covariance. -/
noncomputable def cmp116SourcePi4FullWeakenedCovariance
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ) :
    PhysicalEndomorphism M Q Nc :=
  ∑' n : ℕ,
    cmp116SourcePi4FullWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK s n

/-- At full coupling, each weakened finite layer is the exact generated walk
layer. -/
theorem cmp116SourcePi4FullWeakenedCovarianceLayer_one
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    cmp116SourcePi4FullWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) n =
      cmp116SourcePi4QuotientGeneratedWalkLayer
        (R := R) K hc hmass hK n := by
  classical
  simp [cmp116SourcePi4FullWeakenedCovarianceLayer,
    cmp116SourcePi4QuotientGeneratedWalkLayer,
    cmp116WeakeningMonomial, CMP99AnchoredWalk.term]

/-- The complete weakened covariance recovers the exact inverse at the fully
coupled point. -/
theorem cmp116SourcePi4FullWeakenedCovariance_one_eq_exact
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4FullWeakenedCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      cmp116SourcePi4QuotientExactPatchedCovariance
        K hc hmass hK := by
  rw [cmp116SourcePi4FullWeakenedCovariance]
  apply Eq.symm
  rw [
    cmp116SourcePi4QuotientExactPatchedCovariance_eq_tsum_generatedLayers
      K hsourceRange hrange hc hmass hK hD]
  apply tsum_congr
  intro n
  exact
    (cmp116SourcePi4FullWeakenedCovarianceLayer_one
      (R := R) anchor K hc hmass hK n).symm

/-- The fully coupled complete weakened covariance is a literal matrix right
inverse of the physical precision. -/
theorem cmp116SourcePi4_precision_mul_fullWeakenedCovarianceMatrix_one_eq_one
    {M Q Nc R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116PhysicalEndomorphismComplexMatrix
          (cmp116SourcePi4FullWeakenedCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)) =
      1 := by
  rw [cmp116SourcePi4FullWeakenedCovariance_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]
  exact
    cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
      K hc hmass hK hD

end

end YangMills.RG
