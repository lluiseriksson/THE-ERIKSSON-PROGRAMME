/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CarrierAnchoredLocalizationRegrouping
import YangMills.RG.BalabanCMP116SourcePi4MixedDerivativeLayerLocalization
import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier
import YangMills.RG.BalabanCMP99SourceDomainLargeBlockConnectivity

/-!
# The equation-(80) walk layer anchored at the literal `Pi^4` carrier

CMP116 applies the repeated FTC expansion to a fixed plaquette-localized
equation-(80) contribution.  Its canonical component is the component
containing the distinguished `Pi^4`, not the component containing an
arbitrarily selected derivative coordinate.

Here `Pi^4` is the already constructed literal large-block carrier

`cmp99SourceDomainLargeBlocks (cmp99SourcePi4CollarDomain anchor)`.

For one mixed covariance-derivative walk layer, this file groups the actual
patched-walk summands by the union of precisely those components which meet
that carrier.  The identity is finite and exact.  It is the source-correct
domain dictionary for the covariance contribution to the equation-(80) FTC
tree; it is not yet the total CMP116 activity `V_k(Y, B)`, because the other
fluctuation-action families and the residual `V''_k` have not been added.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Literal large-block carrier of the distinguished source `Pi^4`. -/
noncomputable def cmp102Eq80SourcePi4AnchorCarrier
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp99SourceDomainLargeBlocks (cmp99SourcePi4CollarDomain anchor)

/-- Canonical source domain of one physical patched-walk summand: all and
only the components of `Pi^4 ∪ active(idx)` which meet `Pi^4`. -/
noncomputable def cmp102Eq80SourcePi4WalkLocalizationDomain
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp116CarrierAnchoredLocalizationDomain
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (cmp102Eq80SourcePi4AnchorCarrier anchor)
    (cmp116SourcePi4LayerWalkActive anchor) idx

/-- The literal large-block `Pi^4` anchor carrier is nonempty. -/
theorem cmp102Eq80SourcePi4AnchorCarrier_nonempty
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q) :
    (cmp102Eq80SourcePi4AnchorCarrier anchor).Nonempty := by
  exact nonempty_cmp99SourceDomainLargeBlocks
    (cmp99SourcePi4CollarDomain anchor)

/-- Connectivity of the source-cell collar lifts to connectivity of its
literal large-block carrier. -/
theorem walkConnected_cmp102Eq80SourcePi4AnchorCarrier
    {Q : ℕ} [NeZero Q] (anchor : FinBox 4 Q) :
    walkConnected (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor) := by
  exact walkConnected_cmp99SourceDomainLargeBlocks
    (cmp99SourcePi4CollarDomain anchor)

/-- The complete distinguished `Pi^4` carrier is retained in every source
domain. -/
theorem cmp102Eq80SourcePi4AnchorCarrier_subset_walkLocalizationDomain
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    cmp102Eq80SourcePi4AnchorCarrier anchor ⊆
      cmp102Eq80SourcePi4WalkLocalizationDomain anchor idx := by
  exact
    cmp116Carrier_subset_carrierAnchoredLocalizationDomain
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (cmp116SourcePi4LayerWalkActive anchor) idx

/-- No block outside the distinguished carrier and the literal walk carrier
is inserted into the source domain. -/
theorem cmp102Eq80SourcePi4WalkLocalizationDomain_subset
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    cmp102Eq80SourcePi4WalkLocalizationDomain anchor idx ⊆
      cmp102Eq80SourcePi4AnchorCarrier anchor ∪
        cmp116SourcePi4LayerWalkActive anchor idx := by
  exact
    cmp116CarrierAnchoredLocalizationDomain_subset
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (cmp116SourcePi4LayerWalkActive anchor) idx

/-- The source localization domain is literally the single confined
component rooted at the lower large-block corner of the distinguished source
cell. -/
theorem cmp102Eq80SourcePi4WalkLocalizationDomain_eq_confinedComponent
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    cmp102Eq80SourcePi4WalkLocalizationDomain anchor idx =
      confinedComponent
        (cmp116CoarseFaceAdj 4 (2 * Q))
        (cmp102Eq80SourcePi4AnchorCarrier anchor ∪
          cmp116SourcePi4LayerWalkActive anchor idx)
        (cmp116BlockCorner (M := 2) anchor) := by
  apply cmp116CarrierAnchoredLocalizationDomain_eq_confinedComponent
  · change
      cmp116BlockCorner (M := 2) anchor ∈
        cmp99SourceDomainLargeBlocks
          (cmp99SourcePi4CollarDomain anchor)
    rw [mem_cmp99SourceDomainLargeBlocks_iff]
    change
      cmp99SourceBaseCellOwner
          (cmp116BlockCorner (M := 2) anchor) ∈
        (cmp99SourcePi4CollarDomain anchor).blocks
    simpa [cmp99SourceBaseCellOwner,
      blockSite_cmp116BlockCorner] using
      mem_cmp99SourcePi4CollarCells_self anchor
  · exact walkConnected_cmp102Eq80SourcePi4AnchorCarrier anchor

/-- Every physical equation-(80) walk domain anchored at `Pi^4` is
face-connected on the large-block lattice. -/
theorem walkConnected_cmp102Eq80SourcePi4WalkLocalizationDomain
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (idx : CMP116SourcePi4LayerWalkIndex M Q R n) :
    walkConnected (cmp116CoarseFaceAdj 4 (2 * Q))
      (cmp102Eq80SourcePi4WalkLocalizationDomain anchor idx) := by
  exact cmp116CarrierAnchoredLocalizationDomain_walkConnected
    (cmp116CoarseFaceAdj 4 (2 * Q))
    (cmp102Eq80SourcePi4AnchorCarrier anchor)
    (cmp116SourcePi4LayerWalkActive anchor) idx
    (cmp102Eq80SourcePi4AnchorCarrier_nonempty anchor)
    (walkConnected_cmp102Eq80SourcePi4AnchorCarrier anchor)

/-- One literal physical mixed derivative layer, regrouped by the source
component touching the distinguished `Pi^4` carrier. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_eq_sum_pi4CarrierAnchoredFiber
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col =
      ∑ Y ∈ cmp116CarrierAnchoredLocalizationDomains
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
          (cmp102Eq80SourcePi4AnchorCarrier anchor)
          (cmp116SourcePi4LayerWalkActive anchor),
        cmp116CarrierAnchoredFiberCoefficient
          (cmp116CoarseFaceAdj 4 (2 * Q))
          (Finset.univ :
            Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
          (cmp102Eq80SourcePi4AnchorCarrier anchor)
          (cmp116SourcePi4LayerWalkActive anchor)
          (cmp116SourcePi4MixedDerivativeLayerWalkTerm
            anchor K hc hmass hK sigma S row col) Y := by
  classical
  have hregroup :=
    cmp116_sum_eq_sum_carrierAnchoredFiberCoefficient
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (Finset.univ :
        Finset (CMP116SourcePi4LayerWalkIndex M Q R n))
      (cmp102Eq80SourcePi4AnchorCarrier anchor)
      (cmp116SourcePi4LayerWalkActive anchor)
      (cmp116SourcePi4MixedDerivativeLayerWalkTerm
        anchor K hc hmass hK sigma S row col)
  rw [Fintype.sum_sigma] at hregroup
  simpa [cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative,
    cmp116SourcePi4MixedDerivativeLayerWalkTerm,
    cmp116SourcePi4LayerWalkActive,
    CMP116SourcePi4LayerWalkIndex.walk] using hregroup

end

end YangMills.RG
