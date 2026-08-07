/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389SourceLocalizedDefectGlobalSup
import YangMills.RG.FinitePiLpOwnerWeightedSupKernel

/-!
# PRE-VALIDATION: fixed-rate owner row for the physical CMP99 defect

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

The complete source-localized CMP99 (3.89) estimate supplies a literal
nonnegative block-operator coefficient between localization owners.  At every
reserved rate `0 <= rate < delta0`, the existing volume-uniform shell bound
turns that matrix into the output-fixed weighted row needed by the global
supremum norm.

All three physical species remain visible in the amplitude before the shell
factor.  This module proves no composition theorem, no power bound, no
Neumann inverse, and no strict contraction.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Literal owner-block coefficient read from the complete source-localized
CMP99 (3.89) bound. -/
noncomputable def cmp99Eq389SourceLocalizedRegionalDefectOwnerCoefficient
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon B0 delta0 : ℝ)
    (targetBlock sourceBlock : FinBox 4 (2 * (K * Q))) : ℝ :=
  finiteOwnerExponentialCoefficient finBoxDist
    (16 * cmp99Eq389SourceLocalizedThreeSpeciesBudget
      (L := L) (K := K) P depth epsilon B0 delta0)
    delta0 targetBlock sourceBlock

/-- Literal fixed-rate owner-row budget.  The rate reserve appears only in
the shell factor `delta0 - rate`; the three-species amplitude is unchanged.
-/
noncomputable def cmp99Eq389SourceLocalizedRegionalDefectOwnerRowBudget
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon B0 delta0 rate : ℝ) : ℝ :=
  (16 * cmp99Eq389SourceLocalizedThreeSpeciesBudget
      (L := L) (K := K) P depth epsilon B0 delta0) *
    cmp99OmegaSiteExpSumBound (delta0 - rate)

/-- The literal regional defect has an output-fixed weighted owner row at
every nonnegative rate strictly below the source decay `delta0`. -/
theorem cmp99Eq389SourceLocalizedRegionalDefect_ownerWeightedSup
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
    (B0 delta0 rate : ℝ)
    (C : ∀ cell,
      CMP99Eq389SourceLocalizedThreeSpeciesGreenCertificate
        hL depth epsilon background budget fineSmall hsmall (Omega cell)
        (carrierNonempty cell) B0 delta0)
    (hrate : 0 ≤ rate) (hgap : rate < delta0) :
    FinitePiLpTypedOwnerWeightedSupKernelBound
      (cmp99Eq389SourceLocalizedRegionalDefect
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth epsilon background budget fineSmall hsmall Omega)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizedRegionalDefectOwnerCoefficient
        (L := L) (K := K) P depth epsilon B0 delta0)
      finBoxDist
      (cmp99Eq389SourceLocalizedRegionalDefectOwnerRowBudget
        (L := L) (K := K) P depth epsilon B0 delta0 rate)
      rate := by
  let A := 16 * cmp99Eq389SourceLocalizedThreeSpeciesBudget
    (L := L) (K := K) P depth epsilon B0 delta0
  let S := cmp99OmegaSiteExpSumBound (delta0 - rate)
  have hlocalized :=
    cmp99Eq389SourceLocalizedRegionalDefect_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      P hL depth background budget fineSmall hsmall Omega
      carrierNonempty B0 delta0 C
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hshell (targetBlock : FinBox 4 (2 * (K * Q))) :
      ∑ sourceBlock : FinBox 4 (2 * (K * Q)),
        Real.exp (-((delta0 - rate) *
          (finBoxDist targetBlock sourceBlock : ℝ))) ≤ S := by
    dsimp [S]
    simpa [finBoxDist_comm] using
      finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound_any
        targetBlock (sub_pos.mpr hgap)
  simpa [A, S,
    cmp99Eq389SourceLocalizedRegionalDefectOwnerCoefficient,
    cmp99Eq389SourceLocalizedRegionalDefectOwnerRowBudget] using
    finitePiLpTypedOwnerWeightedSupKernelBound_of_blockLocalized
      (cmp99Eq389SourceLocalizedRegionalDefect
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth epsilon background budget fineSmall hsmall Omega)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist hlocalized hrate hgap hS hshell

end

end YangMills.RG
