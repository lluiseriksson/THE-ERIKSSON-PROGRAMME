/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CenteredConditionedEq80PartialPotential
import YangMills.RG.BalabanCMP102Eq80PhysicalCombinedEq136

/-!
# The centered conditioned partial potential on the direct/native ledger

The earlier partial-potential adapter used one direct-domain index for both
the equation-(80) and Lemma-1 sectors.  The source-facing dictionary now uses
the disjoint ledger `direct ⊔ native`, so the terminal functions must retain
that index literally.

This file installs the already constructed equation-(80) total and residual
on the direct branch and the literal CMP109 Lemma-1 residual on the native
branch.  Spectator and fluctuation variables have their terminal types and
are ignored only because these source activities do not yet depend on them.
No reindexing map, zero native residual, or analytic estimate is introduced.
-/

namespace YangMills.RG

noncomputable section

private abbrev CombinedPartialFineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CombinedPartialCoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CombinedPartialRectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CombinedPartialCoarseField Q Nc →L[ℝ]
    CombinedPartialFineField M Q Nc

private abbrev CombinedPartialBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

/-- Terminal total activity on the canonical direct/native domain ledger. -/
noncomputable def cmp116CenteredConditionedCombinedEq80PartialTotal
    {Index : Type*} {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport : Finset (CombinedPartialBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedPartialCoarseField Q Nc →L[ℝ]
        CombinedPartialCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedPartialFineField M Q Nc →
      CombinedPartialCoarseField Q Nc)
    (V₀ : CombinedPartialFineField M Q Nc → ℝ)
    (Pprop T : CombinedPartialRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    (J : CombinedPartialFineField M Q Nc)
    (gk : ℝ) :
    (Fin nDelta → ℂ) →
      RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc) →
      RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc) →
      Fin (CMP116Eq80Lemma1CombinedDomainCount anchor domains E) →
      CombinedPartialFineField M Q Nc → ℝ :=
  fun sigma _psi _phi =>
    cmp116Eq80Lemma1CombinedTotal
      (cmp102Eq80PhysicalIndexedContourTotal
        anchor domains contourCarrier e K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T DeltaPi J gk)
      (cmp109Lemma1IndexedSourceResidual E V gk D)

/-- Terminal residual on the same canonical direct/native ledger. -/
noncomputable def cmp116CenteredConditionedCombinedEq80PartialResidual
    {Index : Type*} {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport : Finset (CombinedPartialBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedPartialCoarseField Q Nc →L[ℝ]
        CombinedPartialCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedPartialFineField M Q Nc →
      CombinedPartialCoarseField Q Nc)
    (V₀ : CombinedPartialFineField M Q Nc → ℝ)
    (Pprop T : CombinedPartialRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    (J : CombinedPartialFineField M Q Nc)
    (gk : ℝ) :
    (Fin nDelta → ℂ) →
      RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc) →
      RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc) →
      Fin (CMP116Eq80Lemma1CombinedDomainCount anchor domains E) →
      CombinedPartialFineField M Q Nc → ℝ :=
  fun sigma _psi _phi =>
    cmp116Eq80Lemma1CombinedResidual
      (fun i =>
        cmp102Eq80PhysicalIndexedContourResidual
          anchor domains contourCarrier e i K hc hmass hK
          baseCoarseCovariance sigma layerWord choice
          D D₃ V₀ Pprop T DeltaPi J gk)
      (cmp109Lemma1IndexedSourceResidual E V gk D)

@[simp] theorem cmp116CenteredConditionedCombinedEq80PartialTotal_apply
    {Index : Type*} {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport : Finset (CombinedPartialBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedPartialCoarseField Q Nc →L[ℝ]
        CombinedPartialCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedPartialFineField M Q Nc →
      CombinedPartialCoarseField Q Nc)
    (V₀ : CombinedPartialFineField M Q Nc → ℝ)
    (Pprop T : CombinedPartialRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    (J : CombinedPartialFineField M Q Nc)
    (gk : ℝ) (sigma : Fin nDelta → ℂ)
    (psi : RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc))
    (phi : RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc)) :
    cmp116CenteredConditionedCombinedEq80PartialTotal
        spectatorSupport fluctuationSupport anchor domains E V
        contourCarrier e K hc hmass hK baseCoarseCovariance
        layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi =
      cmp116Eq80Lemma1CombinedTotal
        (cmp102Eq80PhysicalIndexedContourTotal
          anchor domains contourCarrier e K hc hmass hK
          baseCoarseCovariance sigma layerWord choice
          D D₃ V₀ Pprop T DeltaPi J gk)
        (cmp109Lemma1IndexedSourceResidual E V gk D) := rfl

@[simp] theorem cmp116CenteredConditionedCombinedEq80PartialResidual_apply
    {Index : Type*} {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport : Finset (CombinedPartialBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedPartialCoarseField Q Nc →L[ℝ]
        CombinedPartialCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedPartialFineField M Q Nc →
      CombinedPartialCoarseField Q Nc)
    (V₀ : CombinedPartialFineField M Q Nc → ℝ)
    (Pprop T : CombinedPartialRectangularFieldMap M Q Nc)
    (DeltaPi : CombinedPartialFineField M Q Nc →L[ℝ]
      CombinedPartialFineField M Q Nc)
    (J : CombinedPartialFineField M Q Nc)
    (gk : ℝ) (sigma : Fin nDelta → ℂ)
    (psi : RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc))
    (phi : RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc)) :
    cmp116CenteredConditionedCombinedEq80PartialResidual
        spectatorSupport fluctuationSupport anchor domains E V
        contourCarrier e K hc hmass hK baseCoarseCovariance
        layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma psi phi =
      cmp116Eq80Lemma1CombinedResidual
        (fun i =>
          cmp102Eq80PhysicalIndexedContourResidual
            anchor domains contourCarrier e i K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T DeltaPi J gk)
        (cmp109Lemma1IndexedSourceResidual E V gk D) := rfl

end

end YangMills.RG
