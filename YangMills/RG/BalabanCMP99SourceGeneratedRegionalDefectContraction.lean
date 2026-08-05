/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay
import YangMills.RG.BalabanCMP99SourceRegionalDefectOverlap
import YangMills.RG.FinitePiLpScalarCommutator

/-!
# PRE-VALIDATION: physical regional defect contraction

The source below is present, but its `.olean` has not yet been materialized
and its results have not yet been verified by the Lean compiler.

This file performs the quantitative part of step 7 below CMP99 (3.88).  It
sums the literal single-cell corrections with the source overlap `16`, then
uses the volume-uniform exponential shell sum and Schur's test.  The final
operator estimate has one explicit physical scalar budget.

The theorem reducing `norm R' < 1` to that budget does not prove the budget
small.  Establishing the literal scalar inequality remains the physical
attainment boundary of window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

private instance instNeZeroSourceRegionalLargeBlockSide
    (M depth : ℕ) [NeZero M] :
    NeZero (cmp99SourceRegionalLargeBlockSide M depth) :=
  ⟨by
    unfold cmp99SourceRegionalLargeBlockSide
    exact (pow_pos (NeZero.pos M) (depth + 2)).ne'⟩

private instance instNeZeroSourceRegionalAmbientSide
    (M Q depth : ℕ) [NeZero M] [NeZero Q] :
    NeZero (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (pow_pos (NeZero.pos M) (depth + 2))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Literal generated physical regional defect, with the partition, regional
cells, ambient precision, coercivity proof and canonical regional Greens all
fixed internally. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalDefect
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp99RegionalGreenDefect
    (cmp99SourceRegionalLargeBlockSquarePartition
      (M := M) (Q := Q) (depth := depth) P)
    (cmp99SourceGeneratedPhysicalRegionalCell P M Q depth)
    (cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) (spacing := spacing)
      (epsilon := epsilon) hM depth background budget fineSmall)
    (cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall)
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth hspacing
      background budget fineSmall hsmall)

/-- Exponential amplitude after paying the source overlap exactly once. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalDefectAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  16 * cmp99SourceGeneratedPhysicalRegionalCorrectionAmplitude
    P M depth spacing epsilon

/-- Exponential rate retained after the commutator--Green composition. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalDefectRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalRegionalGreenRate M depth spacing epsilon / 2

/-- Literal volume-uniform Schur budget of the generated regional defect. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalDefectBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalRegionalDefectAmplitude
      P M depth spacing epsilon *
    cmp99OmegaSiteExpSumBound
      (cmp99SourceGeneratedPhysicalRegionalDefectRate
        M depth spacing epsilon)

/-- Step 7a: the literal physical defect has the cell-independent exponential
kernel estimate after paying exactly the derived overlap `16`. -/
theorem cmp99SourceGeneratedPhysicalRegionalDefect_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (cmp99SourceGeneratedPhysicalRegionalDefect
        (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
        background budget fineSmall hsmall)
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (cmp99SourceGeneratedPhysicalRegionalDefectAmplitude
        P M depth spacing epsilon)
      (cmp99SourceGeneratedPhysicalRegionalDefectRate
        M depth spacing epsilon) := by
  let partition := cmp99SourceRegionalLargeBlockSquarePartition
    (M := M) (Q := Q) (depth := depth) P
  let regions := cmp99SourceGeneratedPhysicalRegionalCell P M Q depth
  let K := cmp99SourceGeneratedPhysicalAmbientPrecision
    (M := M) (Q := Q) (Nc := Nc) (spacing := spacing)
    (epsilon := epsilon) hM depth background budget fineSmall
  let c := cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  let hc := cmp99SourceGeneratedCoercivity_pos
    4 M depth hspacing hsmall
  let hK := isCoerciveCLM_cmp99SourceGeneratedPhysicalAmbientPrecision
    (M := M) (Q := Q) (Nc := Nc) hM depth hspacing
    background budget fineSmall hsmall
  let A := cmp99SourceGeneratedPhysicalRegionalCorrectionAmplitude
    P M depth spacing epsilon
  let rate := cmp99SourceGeneratedPhysicalRegionalDefectRate
    M depth spacing epsilon
  have hcell : ∀ cell,
      FinitePiLpExponentialKernelBound
        (cmp99RegionalGreenCorrection partition regions K hc hK cell)
        (finBoxDist : FinBox 4
            (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
          FinBox 4
            (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
        A rate := by
    intro cell
    simpa [cmp99SourceGeneratedPhysicalRegionalCorrection,
      partition, regions, K, c, hc, hK, A, rate,
      cmp99SourceGeneratedPhysicalRegionalDefectRate] using
        (cmp99SourceGeneratedPhysicalRegionalCorrection_exponentialKernelBound
          (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
          background budget fineSmall hsmall cell)
  have hA : 0 ≤ A := (hcell default).1
  have hrate : 0 < rate := by
    dsimp [rate, cmp99SourceGeneratedPhysicalRegionalDefectRate]
    exact div_pos
      (cmp99SourceGeneratedPhysicalRegionalGreenRate_pos
        M depth hspacing hsmall) (by norm_num)
  have hdefect :=
    cmp99SourceRegionalLargeBlockGreenDefect_exponentialKernelBound
      (M := M) (Q := Q) (depth := depth) (g := SUNLieCoord Nc)
      (P := P) (Omega := regions) (K := K) (c := c)
      hc hK finBoxDist hA hrate hcell
  simpa [cmp99SourceGeneratedPhysicalRegionalDefect,
    cmp99SourceGeneratedPhysicalRegionalDefectAmplitude,
    cmp99SourceGeneratedPhysicalRegionalDefectRate,
    partition, regions, K, c, hc, hK, A, rate] using hdefect

/-- Step 7b: Schur converts the physical exponential estimate into the one
explicit, volume-uniform regional defect budget. -/
theorem norm_cmp99SourceGeneratedPhysicalRegionalDefect_le_budget
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalRegionalDefect
      (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
      background budget fineSmall hsmall‖ ≤
        cmp99SourceGeneratedPhysicalRegionalDefectBudget
          P M depth spacing epsilon := by
  let T := cmp99SourceGeneratedPhysicalRegionalDefect
    (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
    background budget fineSmall hsmall
  let rate := cmp99SourceGeneratedPhysicalRegionalDefectRate
    M depth spacing epsilon
  let rowSum := cmp99OmegaSiteExpSumBound rate
  have hrate : 0 < rate := by
    dsimp [rate, cmp99SourceGeneratedPhysicalRegionalDefectRate]
    exact div_pos
      (cmp99SourceGeneratedPhysicalRegionalGreenRate_pos
        M depth hspacing hsmall) (by norm_num)
  have hrowSum : 0 ≤ rowSum := by
    dsimp [rowSum, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hT :=
    cmp99SourceGeneratedPhysicalRegionalDefect_exponentialKernelBound
      (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
      background budget fineSmall hsmall
  have hsum : ∀ source : FinBox 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)),
      ∑ target,
        Real.exp (-(rate * (finBoxDist source target : ℝ))) ≤ rowSum := by
    intro source
    simpa [finBoxDist_comm, rowSum] using
      finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound_any source hrate
  have hop := finitePiLpOpNorm_le_of_exponentialKernelBound
    T finBoxDist (fun x y => finBoxDist_comm x y) hrowSum hT hsum
  simpa [T, rate, rowSum,
    cmp99SourceGeneratedPhysicalRegionalDefectBudget] using hop

/-- The operator contraction follows from the literal physical scalar
budget.  The premise is deliberately not manufactured from the abstract
joint-regime target: proving it is the remaining attainment boundary of
window 15. -/
theorem norm_cmp99SourceGeneratedPhysicalRegionalDefect_lt_one_of_budget
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (hbudget : cmp99SourceGeneratedPhysicalRegionalDefectBudget
      P M depth spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalRegionalDefect
      (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
      background budget fineSmall hsmall‖ < 1 :=
  (norm_cmp99SourceGeneratedPhysicalRegionalDefect_le_budget
    (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
    background budget fineSmall hsmall).trans_lt hbudget

end

end YangMills.RG
