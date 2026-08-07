/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342RegionalGreenCertificate
import YangMills.RG.BalabanCMP99Eq389SourceLocalizationOwner

/-!
# PRE-VALIDATION: source-localized regional Green package for CMP99 (3.42)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

CMP99 (3.42), printed p. 397, bounds four actions of the same regional
Dirichlet Green on an arbitrary field supported in one localization block:
`G'`, `D G'`, `G' D*`, and `Delta G'`.  Their scale vector is
`[ell^2, ell, ell, 1]`, with `ell = L^(depth+1)`, and their common decay is
measured between source-localization owners rather than the coarser separated
regional cells.

This certificate fixes all four operators definitionally to the canonical
regional Green and the literal regional covariant derivative/Laplacian.  It
does not accept a freely chosen Green family.  The four source estimates are
named source inputs; this module does not prove CMP99 Theorem 3.1, equation
(3.42), the three-species estimate (3.89), or the defect contraction.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ} [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq342SourceLocalizedAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Source-localization owner of an active regional zero-cochain site. -/
noncomputable def cmp99Eq342SourceLocalizedActiveOwner
    (L K Q depth : ℕ) [NeZero L]
    {Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))}
    (x : ActiveGaugeRegion.Site Omega) : FinBox 4 (2 * (K * Q)) :=
  cmp99Eq389SourceLocalizationOwner L K Q depth x.1

/-- Source-localization owner of a physical bond, determined by its initial
fine site. -/
noncomputable def cmp99Eq342SourceLocalizedBondOwner
    (L K Q depth : ℕ) [NeZero L]
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    FinBox 4 (2 * (K * Q)) :=
  cmp99Eq389SourceLocalizationOwner L K Q depth b.1

/-- Source-facing certificate for the four estimates in CMP99 (3.42).

The carrier nonemptiness is an explicit parameter because the finite
supremum norm is only defined on a nonempty source index.  Every bound is on
the same canonical regional Dirichlet Green and uses the exact source
localization owners at scale `L^(depth+1)`. -/
structure CMP99Eq342SourceLocalizedGreenCertificate
    (depth : ℕ)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (spacing : ℝ)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ) : Prop where
  B0_pos : 0 < B0
  delta0_pos : 0 < delta0
  value_bound :
    FinitePiLpTypedBlockLocalizedSupBound
      (cmp99RegionalDirichletGreen Omega A hc hAcoer)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist
      (B0 * (L ^ (depth + 1) : ℝ) ^ 2) delta0
  left_derivative_bound :
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega A hc hAcoer))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist
      (B0 * (L ^ (depth + 1) : ℝ)) delta0
  right_adjoint_derivative_bound :
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99RegionalDirichletGreen Omega A hc hAcoer).comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist
      (B0 * (L ^ (depth + 1) : ℝ)) delta0
  laplacian_bound :
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega A hc hAcoer))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist B0 delta0

/-- Strict positivity of the source amplitude gives the nonnegativity used
by downstream triangle estimates. -/
theorem CMP99Eq342SourceLocalizedGreenCertificate.B0_nonneg
    {depth : ℕ}
    {Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))}
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    {rho : SUNAdjointModel Nc}
    {U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc}
    {spacing : ℝ}
    {A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc)}
    {c : ℝ} {hc : 0 < c} {hAcoer : IsCoerciveCLM A c}
    {B0 delta0 : ℝ}
    (C : CMP99Eq342SourceLocalizedGreenCertificate depth Omega rho U spacing
      A c hc hAcoer B0 delta0) :
    0 ≤ B0 :=
  C.B0_pos.le

end

end YangMills.RG
