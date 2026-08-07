/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389GeneratedMassSourceLocalizedBound
import YangMills.RG.BalabanCMP99Eq389SignedCovariantLinkSourceLocalizedBound
import YangMills.RG.BalabanCMP99Eq389SignedCutoffLaplacianSourceLocalizedBound
import YangMills.RG.BalabanCMP99Eq389ThreeSpeciesPhysicalBound

/-!
# PRE-VALIDATION: source-localized three-species CMP99 (3.89)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

This module assembles the three literal species of CMP99 (3.88) for one
regional cell after specializing every term to the same generated background,
precision and coercivity.  The resulting estimate is the arbitrary-field,
source-localized supremum statement printed in CMP99 (3.89), with the three
budgets still visible before the overlap-cell sum.

It does not sum regional cells, prove the overlap transport in the source
norm, establish the defect contraction, or attain window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389SourceLocalizedThreeSpeciesAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Literal sum of the three regional species in CMP99 (3.88), for one cell
and one source-generated physical background. -/
noncomputable def cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let U := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  let A := cmp99Eq389SourceSeparatedPhysicalPrecision
    hL depth epsilon background budget fineSmall
  let c := cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon
  let hc := cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
    (L := L) depth hsmall
  let hAcoer := isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth background budget fineSmall hsmall
  cmp99Eq389SignedCovariantLinkRegionalCorrection
      (L := L) (K := K) (Q := Q) P depth cell Omega
      (matrixSUNAdjointModel Nc) U A c hc hAcoer +
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection
      (L := L) (Klarge := K) (Q := Q) (Nc := Nc)
      P depth cell Omega A c hc hAcoer +
    cmp99Eq389GeneratedMassRegionalCorrection
      (L := L) (K := K) (Q := Q) P hL depth 1 epsilon background
      budget.toRadiusChain fineSmall cell Omega A c hc hAcoer

/-- A zero right signed cutoff kills the literal sum of all three CMP99
species on a one-site source probe.  This is an exact algebraic statement,
not a numerical estimate of the probe expansion. -/
theorem
    cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection_single_eq_zero_of_value_eq_zero
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc)
    (hzero : cmp99SourceSeparatedSignedLargeBlockCutoff
      P L K Q depth cell source = 0) :
    cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection
        (L := L) (K := K) (Q := Q) P hL depth epsilon background budget
        fineSmall hsmall cell Omega (singleFinitePiLp source v) = 0 := by
  let U := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  let A := cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth epsilon background budget fineSmall
  let c := cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon
  let hc := cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
    (L := L) depth hsmall
  let hAcoer := isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth background budget fineSmall hsmall
  have hfirst :=
    cmp99Eq389SignedCovariantLinkRegionalCorrection_single_eq_zero_of_value_eq_zero
      (L := L) (K := K) (Q := Q) P depth cell Omega
      (matrixSUNAdjointModel Nc) U A c hc hAcoer source v hzero
  have hsecond :=
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection_single_eq_zero_of_value_eq_zero
      (L := L) (Klarge := K) (Q := Q) (Nc := Nc)
      P depth cell Omega A c hc hAcoer source v hzero
  have hthird :=
    cmp99Eq389GeneratedMassRegionalCorrection_single_eq_zero_of_value_eq_zero
      (L := L) (K := K) (Q := Q) P hL depth 1 epsilon background
      budget.toRadiusChain fineSmall cell Omega A c hc hAcoer source v hzero
  change
    cmp99Eq389SignedCovariantLinkRegionalCorrection
          (L := L) (K := K) (Q := Q) P depth cell Omega
          (matrixSUNAdjointModel Nc) U A c hc hAcoer
          (singleFinitePiLp source v) +
        cmp99Eq389SignedCutoffLaplacianRegionalCorrection
          (L := L) (Klarge := K) (Q := Q) (Nc := Nc)
          P depth cell Omega A c hc hAcoer (singleFinitePiLp source v) +
        cmp99Eq389GeneratedMassRegionalCorrection
          (L := L) (K := K) (Q := Q) P hL depth 1 epsilon background
          budget.toRadiusChain fineSmall cell Omega A c hc hAcoer
          (singleFinitePiLp source v) = 0
  simpa only [hfirst, hsecond, hthird, zero_add, add_zero]

/-- The source-facing single-cell budget keeps the three mechanisms of
CMP99 (3.88) separate and contains no overlap factor. -/
noncomputable def cmp99Eq389SourceLocalizedThreeSpeciesBudget
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon B0 delta0 : ℝ) : ℝ :=
  cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K +
    cmp99Eq389SignedCutoffLaplacianSourceBudget P B0 K +
    cmp99Eq389GeneratedMassSourceBudget
      (L := L) (K := K) P depth 1 epsilon B0
        (L ^ (depth + 1) : ℝ)

/-- One source-localized Green certificate fixed definitionally to the same
background, precision, coercivity and rescaled spacing as all three species.
-/
abbrev CMP99Eq389SourceLocalizedThreeSpeciesGreenCertificate
    (hL : 2 ≤ L) (depth : ℕ) (epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (carrierNonempty : Nonempty (ActiveGaugeRegion.Site Omega))
    (B0 delta0 : ℝ) : Prop :=
  letI : Nonempty (ActiveGaugeRegion.Site Omega) := carrierNonempty
  CMP99Eq342SourceLocalizedGreenCertificate depth Omega
    (matrixSUNAdjointModel Nc)
    (cmp99Eq389SourceSeparatedPhysicalBackground L K Q depth Nc background)
    1
    (cmp99Eq389SourceSeparatedPhysicalPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth epsilon background budget fineSmall)
    (cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon)
    (cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
      (L := L) depth hsmall)
    (isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      hL depth background budget fineSmall hsmall)
    B0 delta0

/-- Source-facing single-cell form of CMP99 (3.89).

The input is an arbitrary field supported in one localization-owner fibre;
no expansion into coordinate probes and no fine-fibre cardinality factor is
used.  The overlap-cell sum and defect contraction remain separate. -/
theorem cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection_bound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    {epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (carrierNonempty : Nonempty (ActiveGaugeRegion.Site Omega))
    (B0 delta0 : ℝ)
    (C : CMP99Eq389SourceLocalizedThreeSpeciesGreenCertificate
      hL depth epsilon background budget fineSmall hsmall Omega
      carrierNonempty B0 delta0) :
    FinitePiLpTypedBlockLocalizedSupBound
      (cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth epsilon background budget
        fineSmall hsmall cell Omega)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist
      (cmp99Eq389SourceLocalizedThreeSpeciesBudget
        (L := L) (K := K) P depth epsilon B0 delta0)
      delta0 := by
  letI : Nonempty (ActiveGaugeRegion.Site Omega) := carrierNonempty
  let U := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  let A := cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth epsilon background budget fineSmall
  let c := cmp99Eq389SourceSeparatedPhysicalCoercivity L depth epsilon
  let hc := cmp99Eq389SourceSeparatedPhysicalCoercivity_pos
    (L := L) depth hsmall
  let hAcoer := isCoerciveCLM_cmp99Eq389SourceSeparatedPhysicalPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    hL depth background budget fineSmall hsmall
  have hfirst :=
    cmp99Eq389SignedCovariantLinkRegionalCorrection_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) P depth cell Omega
      (matrixSUNAdjointModel Nc) U A c hc hAcoer B0 delta0 C
  have hsecond :=
    cmp99Eq389SignedCutoffLaplacianRegionalCorrection_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      P depth cell Omega (matrixSUNAdjointModel Nc) U
      A c hc hAcoer B0 delta0 C
  have hthird :=
    cmp99Eq389GeneratedMassRegionalCorrection_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) P hL depth 1 epsilon background
      budget.toRadiusChain fineSmall cell Omega U A c hc hAcoer
      B0 delta0 C
  dsimp [cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection,
    cmp99Eq389SourceLocalizedThreeSpeciesBudget]
  exact finitePiLpTypedBlockLocalizedSupBound_add
    (finitePiLpTypedBlockLocalizedSupBound_add hfirst hsecond) hthird

end

end YangMills.RG
