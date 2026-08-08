/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395PhysicalDistanceDecay
import YangMills.RG.FinitePiLpTypedKernelReindex

/-!
# Reindexing the CMP99 equation (3.95) middle to its source region

The canonical generated tower ends on a recursively exposed terminal-site
type which is propositionally equal to the original physical source region.
This file performs that reindexing by a literal finite equivalence.  It then
transports the fixed-rate kernel estimate to the ordinary source-region
coordinates, where the distance is exactly `finBoxDist` on physical blocks.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- Canonical finite equivalence between generated terminal sites and the
sites of the original physical source region. -/
noncomputable def cmp99Eq395TerminalSiteEquiv
    (Omega : ActiveGaugeRegion 4 (2 * Q)) (depth : ℕ) :
    (cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
      |>.terminalSite) ≃ ActiveGaugeRegion.Site Omega :=
  Equiv.cast (cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1))

set_option maxHeartbeats 4000000 in
/-- The generated global middle, isometrically reindexed to the original
physical source-region carrier. -/
noncomputable def cmp99Eq395GeneratedPhysicalMiddleOnSource
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  finitePiLpTypedKernelReindex
    (cmp99Eq395TerminalSiteEquiv (M := M) Omega depth)
    (cmp99Eq395TerminalSiteEquiv (M := M) Omega depth)
    (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
      budget fineSmall hsmall)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- Reindexing exposes the generated decay directly in the physical block
metric of the original source region, with unchanged amplitude and rate. -/
theorem cmp99Eq395GeneratedPhysicalMiddleOnSource_exponentialKernelBound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
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
      (cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
        background budget fineSmall hsmall)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  have hgenerated :=
    cmp99Eq395GeneratedPhysicalMiddle_physicalDist_exponentialKernelBound
      Omega hM depth hspacing background budget fineSmall hsmall
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex
    (cmp99Eq395TerminalSiteEquiv (M := M) Omega depth)
    (cmp99Eq395TerminalSiteEquiv (M := M) Omega depth)
    (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
      budget fineSmall hsmall)
    (cmp99SourceIteratedLiftPhysicalTerminalDist
      (M := M) Omega (depth + 1)) hgenerated
  let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  have hcast (x : ActiveGaugeRegion.Site Omega) :
      hsite ▸ ((cmp99Eq395TerminalSiteEquiv
        (M := M) Omega depth).symm x) = x := by
    exact cast_cancel_of_opposite_equalities hsite hsite.symm x
  have hdist :
      (fun target source : ActiveGaugeRegion.Site Omega =>
        cmp99SourceIteratedLiftPhysicalTerminalDist
          (M := M) Omega (depth + 1)
          ((cmp99Eq395TerminalSiteEquiv (M := M) Omega depth).symm target)
          ((cmp99Eq395TerminalSiteEquiv (M := M) Omega depth).symm source)) =
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1) := by
    funext target source
    unfold cmp99SourceIteratedLiftPhysicalTerminalDist
    rw [hcast target, hcast source]
  change FinitePiLpTypedExponentialKernelBound
    (finitePiLpTypedKernelReindex
      (cmp99Eq395TerminalSiteEquiv (M := M) Omega depth)
      (cmp99Eq395TerminalSiteEquiv (M := M) Omega depth)
      (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
        budget fineSmall hsmall))
    (fun target source : ActiveGaugeRegion.Site Omega =>
      finBoxDist target.1 source.1)
    (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
    (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4)
  rw [← hdist]
  exact hreindexed

end
end YangMills.RG
