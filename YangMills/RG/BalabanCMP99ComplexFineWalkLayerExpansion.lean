/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexMinimizerWordExpansion

/-!
# Walk-level refinement of the complex CMP99 fine layers

Each fine covariance length layer is a finite sum over a literal head chart
and an admissible physical tail.  This module exposes that dependent finite
index, its exact active carrier, and its matrix contribution.  It is the
source-faithful refinement needed before coarse words can be grouped by the
union of their physical carriers.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

/-- Literal dependent index of one length-`n` source `Pi^4` covariance
walk: a physical head chart and one admissible tail from that head. -/
abbrev CMP99SourcePi4FineWalkIndex
    (M Q R n : ℕ) [NeZero M] [NeZero Q] :=
  Σ head : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)),
    ↥(cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged
        physicalBondDist R)
      head n)

/-- The anchored physical walk represented by a fine-walk index. -/
def cmp99SourcePi4FineWalkIndex.walk
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged
        physicalBondDist R)
      index.1 :=
  ⟨n, index.2⟩

/-- Exact source weakening carrier of one indexed fine walk. -/
noncomputable def cmp99SourcePi4FineWalkIndex.active
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp116SourcePi4QuotientWalkActive
    (M := M) anchor index.1
      (cmp99SourcePi4FineWalkIndex.walk index)

/-- Literal ordered physical operator of one indexed fine walk. -/
noncomputable def cmp99SourcePi4FineWalkIndex.operator
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    FineField M Q Nc →L[ℝ] FineField M Q Nc :=
  (cmp99SourcePi4FineWalkIndex.walk index).term
    (cmp99PhysicalPatchHead
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK)
    (fun _ => cmp99PhysicalPatchContinuation
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK)

/-- Matrix contribution of one indexed physical fine walk. -/
noncomputable def cmp99SourcePi4ComplexFineWalkTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    Matrix (FineCoord M Q Nc) (FineCoord M Q Nc) ℂ :=
  cmp116ComplexWeakeningMonomial
      (cmp99SourcePi4FineWalkIndex.active anchor index) sigma •
    cmp116PhysicalEndomorphismComplexMatrix
      (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK index)

/-- Evaluation of one fine-walk term preserves the source row/output and
column/input convention literally. -/
theorem cmp99SourcePi4ComplexFineWalkTerm_apply
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (index : CMP99SourcePi4FineWalkIndex M Q R n)
    (row col : FineCoord M Q Nc) :
    cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK sigma index row col =
      cmp116ComplexWeakeningMonomial
          (cmp99SourcePi4FineWalkIndex.active anchor index) sigma *
        cmp116ComplexPhysicalOperatorCoefficient
          (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK index)
          col.1 row.1 col.2 row.2 := by
  rw [cmp99SourcePi4ComplexFineWalkTerm,
    Matrix.smul_apply,
    cmp116PhysicalEndomorphismComplexMatrix_apply]
  rfl

/-- A complete complex fine covariance layer is exactly the finite sum of
its literal indexed physical walk matrices. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (n : ℕ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma n =
      ∑ index : CMP99SourcePi4FineWalkIndex M Q R n,
        cmp99SourcePi4ComplexFineWalkTerm
          anchor K hc hmass hK sigma index := by
  classical
  rw [Fintype.sum_sigma]
  ext row col
  simp only [cmp116SourcePi4FullComplexWeakenedCovarianceLayer]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro head _hhead
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro tail _htail
  rw [cmp99SourcePi4ComplexFineWalkTerm_apply]
  rfl

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- One fine walk's contour difference transported into the relative
coarse-middle defect.  Its physical carrier is exactly `index.active`. -/
noncomputable def cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ :=
  complexRectangularSandwichCLM
      (cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
        cmp99SourcePi4ComplexBlockMatrix
          (M := M) (Q := Q) (Nc := Nc))
      (cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc))
    (cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK sigma index -
      cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK (fun _ => 1) index)

/-- Every coarse defect layer is the finite sum of its literal fine-walk
defect terms, retaining the physical carrier of each walk. -/
theorem
    cmp99SourcePi4ComplexCoarseRelativeDefectLayer_eq_sum_fineWalkTerms
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (n : ℕ) :
    cmp99SourcePi4ComplexCoarseRelativeDefectLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma n =
      ∑ index : CMP99SourcePi4FineWalkIndex M Q R n,
        cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
          anchor K hc hmass hK baseCoarseCovariance sigma index := by
  let L :=
    complexRectangularSandwichCLM
      (cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
        cmp99SourcePi4ComplexBlockMatrix
          (M := M) (Q := Q) (Nc := Nc))
      (cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc))
  rw [cmp99SourcePi4ComplexCoarseRelativeDefectLayer,
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms,
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer_eq_sum_fineWalkTerms]
  change L
      ((∑ index : CMP99SourcePi4FineWalkIndex M Q R n,
          cmp99SourcePi4ComplexFineWalkTerm
            anchor K hc hmass hK sigma index) -
        ∑ index : CMP99SourcePi4FineWalkIndex M Q R n,
          cmp99SourcePi4ComplexFineWalkTerm
            anchor K hc hmass hK (fun _ => 1) index) =
    ∑ index : CMP99SourcePi4FineWalkIndex M Q R n,
      L (cmp99SourcePi4ComplexFineWalkTerm
          anchor K hc hmass hK sigma index -
        cmp99SourcePi4ComplexFineWalkTerm
          anchor K hc hmass hK (fun _ => 1) index)
  rw [map_sub, map_sum, map_sum]
  simp_rw [map_sub]
  exact (Finset.sum_sub_distrib _ _).symm

end

end YangMills.RG
