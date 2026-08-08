/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalWalkFiniteSum
import YangMills.RG.BalabanCMP116SourcePi4FullComplexWeakenedCovariance
import YangMills.RG.ComplexWeakeningMonomialDifference

/-!
# Terminal grouping of the complete complex contour defect

The difference `C_n(sigma) - C_n(1)` is grouped by the terminal physical
chart of each forward walk.  The explicit terminal `Finset` is the same one
used by the reverse-counting theorem; its source core is therefore available
for the later partition argument.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Literal source weakening carrier of a raw forward walk pair. -/
noncomputable def cmp116SourcePi4ForwardWalkActive
    {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))) :
    Finset (FinBox 4 (2 * Q)) :=
  (⟨walk.1, walk.2⟩ :
    CMP99GeneralizedWalk Unit
      ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))).active fun chart =>
      cmp99SourceDomainLargeBlocks chart.1.domain ∩
        cmp116SourceSigmaZero anchor

/-- One terminal group of the length-`n` complex covariance defect. -/
noncomputable def cmp116SourcePi4TerminalComplexDefectLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  fun row col =>
    ∑ walk ∈ cmp99PhysicalPatchForwardTerminalWalks
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal,
      (cmp116ComplexWeakeningMonomial
          (cmp116SourcePi4ForwardWalkActive anchor walk) sigma - 1) *
        cmp116ComplexPhysicalOperatorCoefficient
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
          col.1 row.1 col.2 row.2

/-- A terminal complex defect group reads only source coordinates in its
terminal physical core. -/
theorem cmp116SourcePi4TerminalComplexDefectLayer_apply_eq_zero_of_not_mem_core
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsource :
      col.1 ∉ cmp99SourcePi4ChartCore (M := M) terminal.1) :
    cmp116SourcePi4TerminalComplexDefectLayer
        (R := R) anchor K hc hmass hK sigma n terminal row col = 0 := by
  classical
  simp only [cmp116SourcePi4TerminalComplexDefectLayer]
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
            (EuclideanSpace.single col.2 (1 : ℝ))) = 0 := by
    exact
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
  rw [hcoeff, mul_zero]

/-- Summing the terminal defect groups reconstructs the literal difference
between the complete complex layer and its fully coupled value. -/
theorem sum_cmp116SourcePi4TerminalComplexDefectLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ) (n : ℕ) :
    (∑ terminal : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
      cmp116SourcePi4TerminalComplexDefectLayer
        (R := R) anchor K hc hmass hK sigma n terminal) =
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma n -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) n := by
  classical
  funext row col
  simp only [cmp116SourcePi4TerminalComplexDefectLayer,
    Matrix.sum_apply]
  simp_rw [sum_cmp99PhysicalPatchForwardTerminalWalks]
  rw [Matrix.sub_apply]
  simp only [cmp116SourcePi4FullComplexWeakenedCovarianceLayer]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro tail _htail
  simp [cmp116SourcePi4ForwardWalkActive,
    cmp116SourcePi4QuotientWalkActive,
    cmp116SourcePi4ForwardWalkOperator,
    CMP99AnchoredWalk.active,
    CMP99AnchoredWalk.term,
    CMP99AnchoredWalk.toGeneralizedWalk,
    cmp116ComplexWeakeningMonomial]
  ring

end

end YangMills.RG
