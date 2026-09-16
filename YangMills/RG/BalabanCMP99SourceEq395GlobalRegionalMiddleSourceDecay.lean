/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalRegionalMiddleExponentialDecay
import YangMills.RG.BalabanCMP99SourceEq395TerminalReindex

/-!
# Source-coordinate decay of the CMP99 global--regional middle defect

The fixed-rate estimate for the full-to-`Pi^4` defect is initially obtained
on the recursively generated terminal-site types.  This file reindexes both
rectangular legs to the literal physical source regions and proves that the
result is exactly the independently constructed physical-coordinate defect.
No generated carrier remains in the terminal estimate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- The fine-representative distance formula also holds between two
different canonical source-region chains.  The existing square version is
insufficient for the rectangular full-to-regional defect. -/
theorem cmp99SourceIteratedLift_terminalRepresentative_finBoxDist_rectangular
    (OmegaTarget OmegaSource : ActiveGaugeRegion 4 (2 * Q)) (depth : ℕ) :
    let targetRegions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaTarget depth
    let sourceRegions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) OmegaSource depth
    let htarget := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
      (M := M) OmegaTarget depth
    let hsource := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
      (M := M) OmegaSource depth
    ∀ target : targetRegions.terminalSite,
      ∀ source : sourceRegions.terminalSite,
        finBoxDist (targetRegions.terminalRepresentative target).1
            (sourceRegions.terminalRepresentative source).1 =
          M ^ depth * finBoxDist ((htarget ▸ target).1) ((hsource ▸ source).1) := by
  dsimp only
  intro target source
  rw [cmp99SourceIteratedLift_terminalRepresentative_eq_basepoint,
    cmp99SourceIteratedLift_terminalRepresentative_eq_basepoint]
  exact finBoxDist_cmp99GeneratedTerminalBlockBasepoint_eq_mul depth _ _

namespace CMP99SourceDependentOmegaGeometry

/-- The full-to-`Pi^4` middle defect, isometrically reindexed from both
generated terminal carriers to the two original physical source regions. -/
noncomputable def cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ActiveGaugeZeroCochain (cmp99Eq395FullCoarseRegion (Q := Q))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j))
        (SUNLieCoord Nc) :=
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  finitePiLpTypedKernelReindex
    (cmp99Eq395TerminalSiteEquiv (M := M) OmegaLarge depth)
    (cmp99Eq395TerminalSiteEquiv (M := M) OmegaSmall depth)
    (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates hpi5 hM
      depth hspacing background budget fineSmall hsmall)

set_option maxRecDepth 5000 in
set_option synthInstance.maxHeartbeats 3000000 in
set_option maxHeartbeats 10000000 in
/-- The literal source-coordinate full-to-`Pi^4` defect has the same
volume-independent fixed-rate decay as its generated-terminal realization. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM depth
        hspacing background budget fineSmall hsmall)
      (fun target source => M ^ (depth + 1) * finBoxDist target.1 source.1)
      (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 12) := by
  let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
  let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
  let T := D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates
    hpi5 hM depth hspacing background budget fineSmall hsmall
  have hterminal :=
    D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectTerminalCoordinates_exponentialKernelBound
      hpi5 hM depth hspacing background budget fineSmall hsmall
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex
    (cmp99Eq395TerminalSiteEquiv (M := M) OmegaLarge depth)
    (cmp99Eq395TerminalSiteEquiv (M := M) OmegaSmall depth)
    T (D.cmp99Eq395PhysicalGlobalRegionalMiddleDist hpi5 depth) hterminal
  let hsiteSmall := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) OmegaSmall (depth + 1)
  let hsiteLarge := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) OmegaLarge (depth + 1)
  have hcastSmall (x : ActiveGaugeRegion.Site OmegaSmall) :
      hsiteSmall ▸ ((cmp99Eq395TerminalSiteEquiv
        (M := M) OmegaSmall depth).symm x) = x := by
    exact cast_cancel_of_opposite_equalities hsiteSmall hsiteSmall.symm x
  have hcastLarge (x : ActiveGaugeRegion.Site OmegaLarge) :
      hsiteLarge ▸ ((cmp99Eq395TerminalSiteEquiv
        (M := M) OmegaLarge depth).symm x) = x := by
    exact cast_cancel_of_opposite_equalities hsiteLarge hsiteLarge.symm x
  have hdist :
      (fun target : ActiveGaugeRegion.Site OmegaSmall =>
        fun source : ActiveGaugeRegion.Site OmegaLarge =>
          D.cmp99Eq395PhysicalGlobalRegionalMiddleDist hpi5 depth
            ((cmp99Eq395TerminalSiteEquiv
              (M := M) OmegaSmall depth).symm target)
            ((cmp99Eq395TerminalSiteEquiv
              (M := M) OmegaLarge depth).symm source)) =
      (fun target source =>
        M ^ (depth + 1) * finBoxDist target.1 source.1) := by
    funext target source
    unfold cmp99Eq395PhysicalGlobalRegionalMiddleDist
    rw [cmp99SourceIteratedLift_terminalRepresentative_finBoxDist_rectangular,
      hcastSmall target, hcastLarge source]
  change FinitePiLpTypedExponentialKernelBound
    (finitePiLpTypedKernelReindex
      (cmp99Eq395TerminalSiteEquiv (M := M) OmegaLarge depth)
      (cmp99Eq395TerminalSiteEquiv (M := M) OmegaSmall depth) T)
    (fun target source => M ^ (depth + 1) * finBoxDist target.1 source.1)
    (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
      M depth spacing epsilon)
    (cmp99SourceGeneratedCombesThomasRate
      4 M depth spacing epsilon / 12)
  rw [← hdist]
  exact hreindexed

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
