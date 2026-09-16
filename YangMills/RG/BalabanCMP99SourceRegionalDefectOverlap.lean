/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalLargeBlockOverlap
import YangMills.RG.FinitePiLpSourceOverlapSum

/-!
# Source-overlap removal in the CMP99 regional Green defect

The regional defect is the sum

`R' = sum_Pi [h_Pi, Delta'] G'_Pi h_Pi`.

The rightmost multiplier makes the `Pi` summand vanish on a one-site source
probe unless `h_Pi` is active at that source.  Hence the large-block overlap
bound `2^4 = 16`, derived from the same CMP95 partition, removes the total
number of cells from the kernel estimate.  This file deliberately leaves the
uniform single-cell correction estimate visible: deriving its amplitude with
the source `M^-1` gain is the next analytic producer.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {M Q depth : ℕ} [NeZero M] [NeZero Q]
variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

private instance instNeZeroSourceRegionalLargeBlockSide
    (M depth : ℕ) [NeZero M] :
    NeZero (cmp99SourceRegionalLargeBlockSide M depth) :=
  ⟨by
    unfold cmp99SourceRegionalLargeBlockSide
    exact (pow_pos (NeZero.pos M) (depth + 2)).ne'⟩

/-- A zero value of the rightmost square multiplier kills the corresponding
regional correction on a one-site source probe. -/
theorem cmp99RegionalGreenCorrection_single_eq_zero_of_value_eq_zero
    (P : CMP99RegionalFineSquarePartition M Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (cell : FinBox 4 Q) (source : FinBox 4 (M * (2 * Q))) (v : g)
    (hzero : P.value cell source = 0) :
    cmp99RegionalGreenCorrection P Omega K hc hK cell
        (singleFinitePiLp source v) = 0 := by
  unfold cmp99RegionalGreenCorrection
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [cmp99RegionalSquareMultiplier, finitePiLpScalarMultiplier_single,
    hzero, zero_smul]
  have hsingle : singleFinitePiLp source (0 : g) = 0 := by
    apply PiLp.ext
    intro target
    by_cases htarget : target = source
    · subst target
      simp
    · rw [singleFinitePiLp_of_ne (0 : g) htarget]
      rfl
  rw [hsingle, map_zero, map_zero]

/-- A uniform single-cell exponential estimate sums with the literal source
overlap and not with the number of regional cells. -/
theorem cmp99RegionalGreenDefect_exponentialKernelBound_of_sourceOverlap
    (P : CMP99RegionalFineSquarePartition M Q)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4 (M * (2 * Q)))
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (dist : FinBox 4 (M * (2 * Q)) →
      FinBox 4 (M * (2 * Q)) → ℕ)
    {overlap : ℕ} {A rate : ℝ}
    (hA : 0 ≤ A) (hrate : 0 < rate)
    (hoverlap : ∀ source,
      (Finset.univ.filter fun cell => P.value cell source ≠ 0).card ≤ overlap)
    (hcorrection : ∀ cell,
      FinitePiLpExponentialKernelBound
        (cmp99RegionalGreenCorrection P Omega K hc hK cell)
        dist A rate) :
    FinitePiLpExponentialKernelBound
      (cmp99RegionalGreenDefect P Omega K hc hK)
      dist ((overlap : ℝ) * A) rate := by
  unfold cmp99RegionalGreenDefect
  apply finitePiLpExponentialKernelBound_sum_of_sourceOverlap
    (term := fun cell => cmp99RegionalGreenCorrection P Omega K hc hK cell)
    (active := fun cell source => P.value cell source ≠ 0)
    (dist := dist) hA hrate hoverlap
  · intro cell source v hinactive
    apply cmp99RegionalGreenCorrection_single_eq_zero_of_value_eq_zero
      P Omega K hc hK cell source v
    simpa using hinactive
  · exact hcorrection

/-- The source large-block specialization pays exactly the derived
four-dimensional overlap `16`.  No caller supplies an overlap constant. -/
theorem cmp99SourceRegionalLargeBlockGreenDefect_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)))
    (K : GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c)
    (dist : FinBox 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
      FinBox 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
    {A rate : ℝ} (hA : 0 ≤ A) (hrate : 0 < rate)
    (hcorrection : ∀ cell,
      FinitePiLpExponentialKernelBound
        (cmp99RegionalGreenCorrection
          (cmp99SourceRegionalLargeBlockSquarePartition
            (M := M) (Q := Q) (depth := depth) P)
          Omega K hc hK cell)
        dist A rate) :
    FinitePiLpExponentialKernelBound
      (cmp99RegionalGreenDefect
        (cmp99SourceRegionalLargeBlockSquarePartition
          (M := M) (Q := Q) (depth := depth) P)
        Omega K hc hK)
      dist (16 * A) rate := by
  apply cmp99RegionalGreenDefect_exponentialKernelBound_of_sourceOverlap
    (P := cmp99SourceRegionalLargeBlockSquarePartition
      (M := M) (Q := Q) (depth := depth) P)
    (Omega := Omega) (K := K) (hc := hc) (hK := hK)
    (dist := dist) (overlap := 16) hA hrate
  · intro source
    simpa [cmp99SourceRegionalLargeBlockActiveCells] using
      card_cmp99SourceRegionalLargeBlockActiveCells_le_sixteen
        P M Q depth source
  · exact hcorrection

end

end YangMills.RG
