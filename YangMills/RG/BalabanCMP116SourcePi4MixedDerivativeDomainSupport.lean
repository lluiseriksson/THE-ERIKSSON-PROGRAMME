/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4MixedDerivativeDomainCoefficientBound

/-!
# Physical support of complete mixed connected-domain coefficients

The canonical fiber is built from the face-connected component containing
the distinguished differentiated coordinate.  Consequently, coefficients
assigned to a domain not containing that root, or to a domain that is not
face-connected, vanish identically at every walk length and after summation.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- A layer coefficient vanishes when its claimed connected domain does not
contain the distinguished mixed coordinate. -/
theorem
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_eq_zero_of_root_not_mem
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hroot : root ∉ Y) :
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK
      sigma S root row col Y = 0 := by
  classical
  unfold cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
    cmp116AnchoredFiberCoefficient
  apply Finset.sum_eq_zero
  intro idx hidx
  have hfiber := (Finset.mem_filter.mp hidx).2
  have hmem :=
    cmp116Anchor_mem_anchoredLocalizationDomain
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (fun _ : CMP116SourcePi4LayerWalkIndex M Q R n => root)
      (cmp116SourcePi4LayerWalkActive anchor) idx
  exact (hroot (hfiber ▸ hmem)).elim

/-- A layer coefficient vanishes when its claimed domain is not connected
in the literal coarse face graph. -/
theorem
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y) :
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK
      sigma S root row col Y = 0 := by
  classical
  unfold cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
    cmp116AnchoredFiberCoefficient
  apply Finset.sum_eq_zero
  intro idx hidx
  have hfiber := (Finset.mem_filter.mp hidx).2
  have hwalk :=
    cmp116AnchoredLocalizationDomain_walkConnected
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (fun _ : CMP116SourcePi4LayerWalkIndex M Q R n => root)
      (cmp116SourcePi4LayerWalkActive anchor) idx
  exact (hconnected (hfiber ▸ hwalk)).elim

/-- The complete coefficient vanishes off domains containing its root. -/
theorem cmp116SourcePi4MixedDerivativeDomainCoefficient_eq_zero_of_root_not_mem
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hroot : root ∉ Y) :
    cmp116SourcePi4MixedDerivativeDomainCoefficient
      (R := R) anchor K hc hmass hK sigma S root row col Y = 0 := by
  simp only [cmp116SourcePi4MixedDerivativeDomainCoefficient,
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_eq_zero_of_root_not_mem
      anchor K hc hmass hK sigma S root row col Y hroot,
    tsum_zero]

/-- The complete coefficient vanishes off face-connected physical domains. -/
theorem
    cmp116SourcePi4MixedDerivativeDomainCoefficient_eq_zero_of_not_walkConnected
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hconnected :
      ¬walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y) :
    cmp116SourcePi4MixedDerivativeDomainCoefficient
      (R := R) anchor K hc hmass hK sigma S root row col Y = 0 := by
  simp only [cmp116SourcePi4MixedDerivativeDomainCoefficient,
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_eq_zero_of_not_walkConnected
      anchor K hc hmass hK sigma S root row col Y hconnected,
    tsum_zero]

end

end YangMills.RG
