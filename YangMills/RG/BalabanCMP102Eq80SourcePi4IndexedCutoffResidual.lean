/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CutoffCenteredResidual
import YangMills.RG.BalabanCMP102Eq80SourcePi4DomainEnumeration

/-!
# Indexed cutoff residual for literal CMP102 source domains

This module composes the canonical finite indexing of the selected CMP102
source domains with the physical cutoff-centered radial residual estimate.
Membership in the selected family and bilateral inclusion in the canonical
centered region are both generated internally.

The printed rate retains the favorable factor `gk^2 * epsilon1`.  The theorem
does not replace the source third-jet majorant by a free completed residual
bound and does not assert equation (1.36).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

/-- Fully indexed one-domain residual producer. -/
theorem abs_half_inner_cmp116RadialTaylorResidualOperator_eq80IndexedCouplingScaledDomainProjection_le_centeredEnergy_of_printedCutoff
    {M Q Nc L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor D))
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (epsilon1 gk : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hepsilon1 : 0 ≤ epsilon1) (hgk : 0 < gk)
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D)
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (f : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc → ℝ)
    (hf : ContDiff ℝ 3 f)
    (sourceMajorant : ℝ) (hsourceMajorant : 0 ≤ sourceMajorant)
    (hsource : ∀ X,
      cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
        ‖iteratedFDeriv ℝ 3 f
          (cmp109ConstrainedLinearFluctuation (L := M) gk X)‖ ≤
            sourceMajorant) :
    let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor D i
    let Z0 := cmp102Eq80SourcePi4CenteredRegion anchor D P
    let B := physicalBondProjection Y.bondSupport
      (cmp116SourcePhysicalCoordinateCochain b)
    |(1 / 2 : ℝ) * inner ℝ B
        (cmp116RadialTaylorResidualOperator
          (cmp102Eq80CouplingScaledPotential gk f) B
          ((hf.comp
            (cmp109ConstrainedLinearFluctuationCLM
              (M := M) (Q := Q) (Nc := Nc) gk).contDiff).of_le
                (by norm_num)) B)| ≤
      (sourceMajorant *
          (gk ^ 2 * (1 + (M : ℝ) ^ 3) ^ 3) *
          (Real.sqrt (((M ^ 4 * Y.blocks.card) * 4 : ℕ) : ℝ) *
            epsilon1) / 3) / 2 *
        (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
          b ba ^ 2) := by
  dsimp only
  exact
    abs_half_inner_cmp116RadialTaylorResidualOperator_eq80CouplingScaledDomainProjection_le_centeredEnergy_of_printedCutoff
      Dict anchor D (cmp102Eq80SourcePi4DomainAt anchor D i)
      (cmp102Eq80SourcePi4DomainAt_mem anchor D i)
      (cmp102Eq80SourcePi4CenteredRegion anchor D P)
      (cmp102Eq80SourcePi4IndexedLocalizationDomain_bondSupport_subset_centeredRegionInterior
        anchor D P i)
      P epsilon1 gk b hepsilon1 hgk hcutoff
      f hf sourceMajorant hsourceMajorant hsource

end

end YangMills.RG
