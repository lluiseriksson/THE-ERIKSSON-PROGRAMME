/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4MixedDerivativeLocalizationPartial
import YangMills.RG.BalabanCMP116SourcePi4TerminalComplexDefectLayer

/-!
# Terminal grouping of mixed connected-domain derivative layers

The literal mixed derivative terms are simultaneously grouped by their
terminal physical chart and by their canonical connected weakening domain.
Terminal grouping exposes the exact core partition needed for a
volume-independent bound, while domain grouping preserves the CMP116
localization label.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- One forward physical walk contribution with both its mixed carrier and
canonical connected-domain selector inserted literally. -/
noncomputable def cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))) : ℂ :=
  let active := cmp116SourcePi4ForwardWalkActive anchor walk
  if cmp116AnchoredLocalizationDomain
      (cmp116CoarseFaceAdj 4 (2 * Q))
      (fun _ : CMP99PhysicalPatchForwardWalkIndex
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)) => root)
      (cmp116SourcePi4ForwardWalkActive anchor) walk = Y then
    (if S ⊆ active then
      cmp116ComplexWeakeningMonomial (active \ S) sigma
    else 0) *
      cmp116ComplexPhysicalOperatorCoefficient
        (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
        col.1 row.1 col.2 row.2
  else 0

/-- The length-`n`, terminal-chart, connected-domain group of the literal
physical mixed derivative. -/
noncomputable def cmp116SourcePi4TerminalMixedDerivativeDomainLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) : ℂ :=
  ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal,
    cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
      anchor K hc hmass hK sigma S root Y row col walk

/-- A terminal-domain mixed group reads only source coordinates in its
terminal physical core. -/
theorem
    cmp116SourcePi4TerminalMixedDerivativeDomainLayer_eq_zero_of_not_mem_core
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsource :
      col.1 ∉ cmp99SourcePi4ChartCore (M := M) terminal.1) :
    cmp116SourcePi4TerminalMixedDerivativeDomainLayer
      (R := R) anchor K hc hmass hK sigma S root Y n terminal row col = 0 := by
  classical
  simp only [cmp116SourcePi4TerminalMixedDerivativeDomainLayer]
  apply Finset.sum_eq_zero
  intro walk hwalk
  have hterminal :=
    terminalDomain_eq_of_mem_cmp99PhysicalPatchForwardTerminalWalks
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal walk hwalk
  have hzero :
      cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk
          (singlePhysicalBondCochain col.1
            (EuclideanSpace.single col.2 (1 : ℝ))) = 0 :=
    cmp99PhysicalPatchWalk_term_apply_eq_zero_of_not_mem_terminalCore
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK
      (⟨walk.1, walk.2⟩ :
        CMP99GeneralizedWalk Unit
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)))
      col.1 (EuclideanSpace.single col.2 (1 : ℝ))
      (by simpa [hterminal] using hsource)
  have hcoeff :
      cmp116ComplexPhysicalOperatorCoefficient
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
          col.1 row.1 col.2 row.2 = 0 := by
    simp [cmp116ComplexPhysicalOperatorCoefficient,
      cmp116PhysicalOperatorCoefficient, hzero]
  unfold cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm
  split_ifs <;> simp [hcoeff]

/-- Summing terminal groups reconstructs exactly the previously defined
connected-domain coefficient of the mixed layer. -/
theorem sum_cmp116SourcePi4TerminalMixedDerivativeDomainLayer
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    (∑ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      cmp116SourcePi4TerminalMixedDerivativeDomainLayer
        (R := R) anchor K hc hmass hK sigma S root Y n
        terminal row col) =
      cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
        (R := R) (n := n) anchor K hc hmass hK
        sigma S root row col Y := by
  classical
  simp only [cmp116SourcePi4TerminalMixedDerivativeDomainLayer]
  simp_rw [sum_cmp99PhysicalPatchForwardTerminalWalks]
  unfold cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
    cmp116AnchoredFiberCoefficient
  rw [Finset.sum_filter, Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tail _htail
  simp [cmp116SourcePi4ForwardWalkMixedDerivativeDomainTerm,
    cmp116AnchoredLocalizationDomain,
    cmp116SourcePi4MixedDerivativeLayerWalkTerm,
    cmp116SourcePi4ForwardWalkActive,
    cmp116SourcePi4LayerWalkActive,
    cmp116SourcePi4QuotientWalkActive,
    cmp116SourcePi4ForwardWalkOperator,
    CMP116SourcePi4LayerWalkIndex.walk,
    CMP99AnchoredWalk.active,
    CMP99AnchoredWalk.term,
    CMP99AnchoredWalk.toGeneralizedWalk]

end

end YangMills.RG
