/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCThirdFieldContDiff
import YangMills.RG.BalabanCMP102Eq80SourcePi4DomainEnumeration
import YangMills.RG.BalabanCMP102Eq80CouplingScaledTaylorSplit

/-!
# The literal indexed physical equation-(80) residual

This module names the concrete coupling-scaled Taylor residual attached to one
canonically indexed CMP102 source domain.  Both the localized-energy estimate
and the printed equation-(1.36) estimate use this exact object.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
extra axioms.
-/

namespace YangMills.RG

noncomputable section

private abbrev IndexedResidualFineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))] [NeZero Nc] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev IndexedResidualCoarseField (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] [NeZero Nc] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev IndexedResidualRectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] :=
  IndexedResidualCoarseField Q Nc →L[ℝ]
    IndexedResidualFineField M Q Nc

/-- The literal coupling-scaled Taylor residual of the indexed physical
equation-(80) FTC potential.  This is the concrete `V''_k(Y, B)` supplied to
the CMP116 residual slot. -/
noncomputable def cmp102Eq80PhysicalIndexedCouplingScaledResidual
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : IndexedResidualFineField M Q Nc →L[ℝ]
      IndexedResidualFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      IndexedResidualCoarseField Q Nc →L[ℝ]
        IndexedResidualCoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : IndexedResidualFineField M Q Nc →
      IndexedResidualCoarseField Q Nc)
    (V₀ : IndexedResidualFineField M Q Nc → ℝ)
    (Pprop T : IndexedResidualRectangularFieldMap M Q Nc)
    (Δπ : IndexedResidualFineField M Q Nc →L[ℝ]
      IndexedResidualFineField M Q Nc)
    (J : IndexedResidualFineField M Q Nc)
    (gk : ℝ) (B : IndexedResidualFineField M Q Nc) : ℝ :=
  let Y :=
    cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
  let f : IndexedResidualFineField M Q Nc → ℝ := fun A =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
  cmp102Eq80CouplingScaledTotalTaylorResidual gk f B

end

end YangMills.RG
