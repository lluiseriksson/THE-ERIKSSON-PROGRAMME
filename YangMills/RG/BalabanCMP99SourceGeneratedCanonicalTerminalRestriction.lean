/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedLiteralTerminalRestriction
import YangMills.RG.BalabanCMP99SourceGeneratedTerminalCoordinates

/-!
# Canonical physical coordinates for the CMP99 terminal restriction

The recursive characterization is specialized here to the canonical
iterated lifts of two nested source regions.  The first endpoint identifies
the depth-zero map literally with physical restriction.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- At depth zero the canonical iterated-lift terminal restriction is the
literal physical restriction between the two source regions. -/
theorem cmp99SourceIteratedLiftTerminalRestriction_zero
    {OmegaSmall OmegaLarge : ActiveGaugeRegion d N}
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    cmp99SourceIteratedLiftTerminalRestriction hsub hd hM rho 0 spacing
        epsilon background chain fineSmall =
      cmp99NestedActiveRegionRestriction
        (g := SUNLieCoord Nc) OmegaSmall OmegaLarge := by
  simpa [cmp99SourceIteratedLiftTerminalRestriction,
    cmp99SourceIteratedLift_nestedRegionChains,
    cmp99SourceIteratedLiftActiveRegionChain] using
    (CMP99SourceNestedRegionChains.terminalRestriction_stop
      (M := M) OmegaSmall OmegaLarge hsub hd hM rho spacing epsilon
      background chain fineSmall)

/-- Two heterogeneously equal terminal maps become literally equal after
transport to the same pair of physical Hilbert bundles. -/
theorem cmp99SourceTerminalCLMTransport_eq_of_heq
    {E F G H E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F') (hG : G = E') (hH : H = F')
    (C : E.carrier →L[ℝ] F.carrier)
    (D : G.carrier →L[ℝ] H.carrier) (hCD : HEq C D) :
    cmp99SourceTerminalCLMTransport hE hF C =
      cmp99SourceTerminalCLMTransport hG hH D := by
  subst E'
  subst F'
  subst G
  subst H
  exact eq_of_heq hCD

end

end YangMills.RG
