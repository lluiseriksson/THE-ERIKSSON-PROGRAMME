/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389SourceLocalizedThreeSpecies
import YangMills.RG.BalabanCMP99Eq389SourceOwnerOverlap
import YangMills.RG.FinitePiLpBlockLocalizedSupOverlapSum

/-!
# The source-localized CMP99 (3.89) regional defect

This module was compiler-verified at exact source checkpoint
`a814d95ac5bb20fa8bfe8871e8764caf2353153b` in cold GitHub Actions run
`31180210309`; its two audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

This module performs the literal regional-cell sum after the three species of
CMP99 (3.88) have been assembled for one cell.  Inactive cells are eliminated
exactly by the common right signed cutoff, and the owner-fibre geometry then
pays the single source overlap `2^4 = 16`.

The conclusion is still a source-localized action estimate.  It does not turn
that estimate into an operator-norm contraction and therefore does not yet
attain window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Literal sum over regional cells of the three source-generated species in
CMP99 (3.88). -/
noncomputable def cmp99Eq389SourceLocalizedRegionalDefect
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  ∑ cell, cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    P hL depth epsilon background budget
      fineSmall hsmall cell (Omega cell)

/-- Summing the complete physical regional family costs exactly the derived
source-owner overlap `16`.  The per-cell three-species budget remains literal,
and no ambient-volume cardinality or probe estimate is introduced. -/
theorem cmp99Eq389SourceLocalizedRegionalDefect_blockLocalizedSupBound
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    {epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1) 1 epsilon < 1)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (carrierNonempty : ∀ cell, Nonempty (ActiveGaugeRegion.Site (Omega cell)))
    (B0 delta0 : ℝ)
    (C : ∀ cell,
      CMP99Eq389SourceLocalizedThreeSpeciesGreenCertificate
        hL depth epsilon background budget fineSmall hsmall (Omega cell)
        (carrierNonempty cell) B0 delta0) :
    FinitePiLpTypedBlockLocalizedSupBound
      (cmp99Eq389SourceLocalizedRegionalDefect
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth epsilon background budget
        fineSmall hsmall Omega)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist
      (16 * cmp99Eq389SourceLocalizedThreeSpeciesBudget
        (L := L) (K := K) P depth epsilon B0 delta0)
      delta0 := by
  classical
  let A := cmp99Eq389SourceLocalizedThreeSpeciesBudget
    (L := L) (K := K) P depth epsilon B0 delta0
  have hcell (cell : FinBox 4 Q) :
      FinitePiLpTypedBlockLocalizedSupBound
        (cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          P hL depth epsilon background budget
          fineSmall hsmall cell (Omega cell))
        (cmp99Eq389SourceLocalizationOwner L K Q depth)
        (cmp99Eq389SourceLocalizationOwner L K Q depth)
        finBoxDist A delta0 := by
    exact cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection_bound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      P hL depth background budget fineSmall
      hsmall cell (Omega cell) (carrierNonempty cell) B0 delta0 (C cell)
  let sample : FinBox 4 Q := Classical.choice inferInstance
  have hsample := hcell sample
  unfold cmp99Eq389SourceLocalizedRegionalDefect
  change FinitePiLpTypedBlockLocalizedSupBound
    (∑ cell, cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      P hL depth epsilon background budget
      fineSmall hsmall cell (Omega cell))
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    finBoxDist ((16 : ℝ) * A) delta0
  apply finitePiLpTypedBlockLocalizedSupBound_sum_of_sourceOwnerOverlap
    (term := fun cell =>
      cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth epsilon background budget
        fineSmall hsmall cell (Omega cell))
    (active := fun cell owner =>
      cell ∈ cmp99Eq389SourceOwnerActiveCellWindow L K Q depth owner)
    (sourceOwner := cmp99Eq389SourceLocalizationOwner L K Q depth)
    (targetOwner := cmp99Eq389SourceLocalizationOwner L K Q depth)
    (dist := finBoxDist) hsample.1 hsample.2.1
  · intro owner
    calc
      (Finset.univ.filter fun cell =>
          cell ∈ cmp99Eq389SourceOwnerActiveCellWindow
            L K Q depth owner).card ≤
          (cmp99Eq389SourceOwnerActiveCellWindow
            L K Q depth owner).card := by
        apply Finset.card_le_card
        intro cell hcell
        exact (Finset.mem_filter.mp hcell).2
      _ ≤ 16 :=
        card_cmp99Eq389SourceOwnerActiveCellWindow_le_sixteen
          L K Q depth owner
  · intro cell source v hinactive
    apply
      cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection_single_eq_zero_of_value_eq_zero
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth epsilon background budget
        fineSmall hsmall cell (Omega cell) source v
    by_contra hcutoff
    exact hinactive
      (mem_cmp99Eq389SourceOwnerActiveCellWindow_of_signedCutoff_ne_zero
        P L K Q depth cell source hcutoff)
  · exact hcell

end

end YangMills.RG
