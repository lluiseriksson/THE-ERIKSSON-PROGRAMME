/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalRegionalMiddleSourceDecay
import YangMills.RG.BalabanCMP99SourceGeneratedNestedRestrictionAdjoint

/-!
# Source-coordinate adjoint decay of the CMP99 global--regional middle defect

The rectangular defect is already controlled from the full source region to
the physical `Pi^4` region.  Its adjoint is the orientation required by the
ambient left defect in equation (3.95); the same amplitude and rate survive
with the two physical legs interchanged.
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

namespace CMP99SourceDependentOmegaGeometry

/-- The adjoint full-to-`Pi^4` source defect has the same fixed-rate,
volume-independent kernel bound in the reverse physical orientation. -/
theorem cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_adjoint_exponentialKernelBound
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
    let OmegaSmall := D.operatorCoarseRegion hpi5 (cmp99OmegaPi4Index j)
    let OmegaLarge := cmp99Eq395FullCoarseRegion (Q := Q)
    FinitePiLpTypedExponentialKernelBound
      (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource hpi5 hM depth
        hspacing background budget fineSmall hsmall).adjoint
      (fun target : ActiveGaugeRegion.Site OmegaLarge =>
        fun source : ActiveGaugeRegion.Site OmegaSmall =>
          M ^ (depth + 1) * finBoxDist source.1 target.1)
      (cmp99Eq395PhysicalGlobalRegionalMiddleDecayAmplitude
        M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 12) := by
  dsimp only
  exact finitePiLpTypedExponentialKernelBound_adjoint _ _
    (D.cmp99Eq395PhysicalGlobalRegionalMiddleDefectOnSource_exponentialKernelBound
      hpi5 hM depth hspacing background budget fineSmall hsmall)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
