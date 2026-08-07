/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389SourceLocalizedDefect
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay
import YangMills.RG.FinitePiLpBlockLocalizedSupGlobal

/-!
# PRE-VALIDATION: global supremum bound for the source-localized CMP99 defect

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

The sealed source-localized CMP99 (3.89) estimate is first applied to each
complete source-owner fibre.  The exact owner decomposition and the existing
four-dimensional volume-uniform shell bound then give a global finite-supremum
action estimate.

The displayed budget retains all three physical species before multiplication
by the shell sum: the first and third terms are generally `K^-1`, while only
the cutoff-Laplacian term is `K^-2`.  This module proves no strict contraction,
no fixed-rate bound on powers, and no Neumann inverse.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Complete global-supremum budget obtained from one source-localized CMP99
(3.89) application and the volume-uniform owner-shell sum. -/
noncomputable def cmp99Eq389SourceLocalizedRegionalDefectGlobalSupBudget
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (epsilon B0 delta0 : ℝ) : ℝ :=
  (16 * cmp99Eq389SourceLocalizedThreeSpeciesBudget
      (L := L) (K := K) P depth epsilon B0 delta0) *
    cmp99OmegaSiteExpSumBound delta0

/-- The literal source-localized regional defect acts globally on the finite
supremum norm with no owner-count or fine-fibre-cardinality factor. -/
theorem finitePiLpSupNorm_cmp99Eq389SourceLocalizedRegionalDefect_le
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
        (carrierNonempty cell) B0 delta0)
    (f : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    finitePiLpSupNorm
        (cmp99Eq389SourceLocalizedRegionalDefect
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          P hL depth epsilon background budget fineSmall hsmall Omega f) ≤
      cmp99Eq389SourceLocalizedRegionalDefectGlobalSupBudget
          (L := L) (K := K) P depth epsilon B0 delta0 *
        finitePiLpSupNorm f := by
  let A := 16 * cmp99Eq389SourceLocalizedThreeSpeciesBudget
    (L := L) (K := K) P depth epsilon B0 delta0
  let S := cmp99OmegaSiteExpSumBound delta0
  have hlocalized :=
    cmp99Eq389SourceLocalizedRegionalDefect_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      P hL depth background budget fineSmall hsmall Omega
      carrierNonempty B0 delta0 C
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hshell (target : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
      ∑ owner : FinBox 4 (2 * (K * Q)),
        Real.exp (-(delta0 *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth target)
            owner : ℝ))) ≤ S := by
    dsimp [S]
    simpa [finBoxDist_comm] using
      finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound_any
        (cmp99Eq389SourceLocalizationOwner L K Q depth target)
        hlocalized.2.1
  change finitePiLpSupNorm
      (cmp99Eq389SourceLocalizedRegionalDefect
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth epsilon background budget fineSmall hsmall Omega f) ≤
    (A * S) * finitePiLpSupNorm f
  exact finitePiLpSupNorm_map_le_of_blockLocalized
    (cmp99Eq389SourceLocalizedRegionalDefect
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      P hL depth epsilon background budget fineSmall hsmall Omega)
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    (cmp99Eq389SourceLocalizationOwner L K Q depth)
    finBoxDist hlocalized hS hshell f

end

end YangMills.RG
