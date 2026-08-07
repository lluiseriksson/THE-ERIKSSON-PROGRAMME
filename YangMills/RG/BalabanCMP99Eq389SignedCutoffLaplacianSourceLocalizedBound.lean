/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342SourceLocalizedGreenCertificate
import YangMills.RG.BalabanCMP99Eq389SignedCutoffLaplacianPhysicalBound
import YangMills.RG.FinitePiLpBlockLocalizedSupAlgebra

/-!
# PRE-VALIDATION: source-localized second species of CMP99 (3.89)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

This module applies the source-facing Green estimate of CMP99 (3.42) to the
literal signed cutoff-Laplacian species in (3.88).  The input is an arbitrary
field supported in one source-localization block and measured in the finite
supremum norm.  No expansion into one-site probes occurs.

The result is one regional cell before the overlap-16 sum.  It does not prove
the complete (3.89) estimate or the defect contraction.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389SourceLocalizedSecondAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- The literal second species for one regional cell obeys the printed
source-localized supremum estimate, with the exact `K^-2` amplitude already
present before the cell sum. -/
theorem
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection_blockLocalizedSupBound
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      depth Omega rho U 1 A c hc hAcoer B0 delta0) :
    FinitePiLpTypedBlockLocalizedSupBound
      (cmp99Eq389SignedCutoffLaplacianRegionalCorrection
        (L := L) (Klarge := K) (Q := Q) (Nc := Nc)
        P depth cell Omega A c hc hAcoer)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist
      (cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 K)
      delta0 := by
  let hcutoff : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℝ :=
    cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
  let coefficient : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℝ :=
    cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
      (L := L) (K := K) P depth cell
  let beta : ℝ := (48 * P.secondDerivBound) /
    cmp99SourceSeparatedLargeBlockCutoffScale L K depth ^ 2
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    exact div_nonneg
      (mul_nonneg (by norm_num) P.secondDerivBound_nonneg) (sq_nonneg _)
  have hcutoff_le : ∀ source, ‖hcutoff source‖ ≤ 1 := by
    intro source
    exact
      (cmp99SourceSeparatedSignedLargeBlockSquarePartition
        (L := L) (K := K) (Q := Q) (depth := depth) P).norm_value_le_one
          cell source
  have hgreen : FinitePiLpTypedBlockLocalizedSupBound
      (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist (B0 * (L ^ (depth + 1) : ℝ) ^ 2) delta0 := by
    unfold cmp99RegionalExtendedDirichletGreen
    apply finitePiLpTypedBlockLocalizedSupBound_extend_comp_restrictZeroCLM
    simpa [cmp99Eq342SourceLocalizedActiveOwner] using C.value_bound
  have hgreenCut :=
    finitePiLpTypedBlockLocalizedSupBound_comp_scalarMultiplier_right
      hcutoff (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer)
      hcutoff_le hgreen
  have hcoefficient : ∀ target, ‖coefficient target‖ ≤ beta := by
    intro target
    exact norm_cmp99SourceSeparatedSignedCutoffLaplacianCoefficient_le
      (L := L) (K := K) P depth cell target
  have hfull :=
    finitePiLpTypedBlockLocalizedSupBound_comp_scalarMultiplier_left
      coefficient
      ((cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer).comp
        (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) hcutoff))
      hbeta hcoefficient hgreenCut
  have hamp :
      beta * (B0 * (L ^ (depth + 1) : ℝ) ^ 2) =
        cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 K := by
    calc
      beta * (B0 * (L ^ (depth + 1) : ℝ) ^ 2) =
          B0 * (beta * (L ^ (depth + 1) : ℝ) ^ 2) := by ring
      _ = B0 * ((12 * P.secondDerivBound) / (K : ℝ) ^ 2) := by
        rw [cmp99SourceSeparatedSignedCutoffLaplacianBudget_mul_range_sq]
      _ = cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 K := by
        unfold cmp99Eq389SignedCutoffLaplacianSourceBudget
        ring
  simpa [cmp99Eq389SignedCutoffLaplacianRegionalCorrection, hcutoff,
    coefficient, hamp] using hfull

end

end YangMills.RG
