/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexFineHeadTailWordExpansion
import YangMills.RG.BalabanCMP116WeakeningMultiplicity

/-!
# Multiplicity expansion of literal complex fine-head/tail words

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations are not yet compiler-verified.

The literal CMP99 word is an ordered product of physical matrices.  Its
weakening dependence is scalar, but overlapping walk carriers can occur more
than once.  This module extracts those scalars without commuting any matrix
factors and expands the resulting product by the exact multiplicity algebra.

The conclusion is algebraic only.  It neither estimates the resulting
monomials nor identifies the connected carrier required by CMP116 Lemma 1.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- Scalar extraction from a finite ordered product of square matrices.
No matrix factors are reordered. -/
theorem cmp99OrderedFinProduct_smul_matrix
    {Index : Type*} [Fintype Index] [DecidableEq Index] :
    ∀ {n : ℕ} (scalar : Fin n → ℂ)
      (matrix : Fin n → Matrix Index Index ℂ),
      cmp99OrderedFinProduct (fun i => scalar i • matrix i) =
        cmp99OrderedFinProduct scalar • cmp99OrderedFinProduct matrix := by
  intro n
  induction n with
  | zero =>
      intro scalar matrix
      simp
  | succ n ih =>
      intro scalar matrix
      rw [cmp99OrderedFinProduct_succ,
        cmp99OrderedFinProduct_succ,
        cmp99OrderedFinProduct_succ,
        ih]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm]

/-- For scalar factors the ordered list product agrees with the canonical
finite product.  This bridge is used only after all noncommutative matrix
factors have been separated. -/
theorem cmp99OrderedFinProduct_complex_eq_finset_prod :
    ∀ {n : ℕ} (scalar : Fin n → ℂ),
      cmp99OrderedFinProduct scalar = ∏ i, scalar i := by
  intro n
  induction n with
  | zero =>
      intro scalar
      simp
  | succ n ih =>
      intro scalar
      rw [cmp99OrderedFinProduct_succ, Fin.prod_univ_succ, ih]

/-- Sigma-independent matrix carried by one literal physical fine walk. -/
noncomputable def cmp99SourcePi4ComplexFineWalkBaseTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    Matrix (FineCoord M Q Nc) (FineCoord M Q Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK index)

theorem cmp99SourcePi4ComplexFineWalkTerm_eq_smul_base
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK sigma index =
      cmp116ComplexWeakeningMonomial
          (cmp99SourcePi4FineWalkIndex.active anchor index) sigma •
        cmp99SourcePi4ComplexFineWalkBaseTerm K hc hmass hK index := by
  rfl

/-- Sigma-independent rectangular sandwich below one coarse defect layer. -/
noncomputable def cmp99SourcePi4ComplexCoarseFineWalkDefectBaseTerm
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (index : CMP99SourcePi4FineWalkIndex M Q R n) :
    Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ :=
  complexRectangularSandwichCLM
      (cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance *
        cmp99SourcePi4ComplexBlockMatrix
          (M := M) (Q := Q) (Nc := Nc))
      (cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc))
    (cmp99SourcePi4ComplexFineWalkBaseTerm K hc hmass hK index)

/-- One physical coarse defect factor is exactly `(m(sigma) - 1)` times a
sigma-independent matrix. -/
theorem cmp99SourcePi4ComplexCoarseFineWalkDefectTerm_eq_smul_base
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
    cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
        anchor K hc hmass hK baseCoarseCovariance sigma index =
      (cmp116ComplexWeakeningMonomial
          (cmp99SourcePi4FineWalkIndex.active anchor index) sigma - 1) •
        cmp99SourcePi4ComplexCoarseFineWalkDefectBaseTerm
          K hc hmass hK baseCoarseCovariance index := by
  unfold cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
  rw [cmp99SourcePi4ComplexFineWalkTerm_eq_smul_base,
    cmp99SourcePi4ComplexFineWalkTerm_eq_smul_base]
  simp only [cmp116ComplexWeakeningMonomial, Finset.prod_const_one,
    one_smul, sub_smul, map_sub, map_smul]
  rfl

/-- Scalar product contributed by the chosen tail walks. -/
noncomputable def cmp99SourcePi4ComplexCoarseFineWalkTailScalar
    {M Q R n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) : ℂ :=
  cmp99OrderedFinProduct fun i =>
    cmp116ComplexWeakeningMonomial
        (cmp99SourcePi4FineWalkIndex.active anchor (choice i)) sigma - 1

/-- Ordered sigma-independent matrix word below the coarse layers. -/
noncomputable def cmp99SourcePi4ComplexCoarseFineWalkTailBase
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ :=
  cmp99OrderedFinProduct fun i =>
    -cmp99SourcePi4ComplexCoarseFineWalkDefectBaseTerm
      K hc hmass hK baseCoarseCovariance (choice i)

theorem cmp99SourcePi4ComplexCoarseFineWalkWordTerm_eq_smul_base
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
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
        anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice =
      cmp99SourcePi4ComplexCoarseFineWalkTailScalar anchor sigma choice •
        cmp99SourcePi4ComplexCoarseFineWalkTailBase
          K hc hmass hK baseCoarseCovariance choice := by
  unfold cmp99SourcePi4ComplexCoarseFineWalkWordTerm
  unfold cmp99DependentOrderedProduct
  have hfactor :
      (fun i : Fin n =>
          -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
            anchor K hc hmass hK baseCoarseCovariance sigma (choice i)) =
        (fun i : Fin n =>
          (cmp116ComplexWeakeningMonomial
              (cmp99SourcePi4FineWalkIndex.active anchor (choice i)) sigma - 1) •
            (-cmp99SourcePi4ComplexCoarseFineWalkDefectBaseTerm
              K hc hmass hK baseCoarseCovariance (choice i))) := by
    funext i
    rw [cmp99SourcePi4ComplexCoarseFineWalkDefectTerm_eq_smul_base]
    simpa only [smul_neg]
  rw [hfactor, cmp99OrderedFinProduct_smul_matrix]
  rfl

/-- Sigma-independent matrix part of a complete literal fine-head/tail word. -/
noncomputable def cmp99SourcePi4ComplexFineHeadTailWordBase
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  (cmp99SourcePi4ComplexFineWalkBaseTerm K hc hmass hK head *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)) *
    cmp99SourcePi4ComplexCoarseFineWalkTailBase
      K hc hmass hK baseCoarseCovariance choice *
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance

/-- Exact scalar coefficient of a complete literal word. -/
noncomputable def cmp99SourcePi4ComplexFineHeadTailScalar
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) : ℂ :=
  cmp116ComplexWeakeningMonomial
      (cmp99SourcePi4FineWalkIndex.active anchor head) sigma *
    cmp99SourcePi4ComplexCoarseFineWalkTailScalar anchor sigma choice

theorem cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_smul_base
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance sigma head layerWord choice =
      cmp99SourcePi4ComplexFineHeadTailScalar anchor sigma head choice •
        cmp99SourcePi4ComplexFineHeadTailWordBase
          K hc hmass hK baseCoarseCovariance head choice := by
  unfold cmp99SourcePi4ComplexFineHeadTailWordTerm
  rw [cmp99SourcePi4ComplexFineWalkTerm_eq_smul_base,
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm_eq_smul_base]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  unfold cmp99SourcePi4ComplexFineHeadTailScalar
  change
    (cmp99SourcePi4ComplexCoarseFineWalkTailScalar anchor sigma choice *
        cmp116ComplexWeakeningMonomial
          (cmp99SourcePi4FineWalkIndex.active anchor head) sigma) •
        cmp99SourcePi4ComplexFineHeadTailWordBase
          K hc hmass hK baseCoarseCovariance head choice =
      (cmp116ComplexWeakeningMonomial
          (cmp99SourcePi4FineWalkIndex.active anchor head) sigma *
        cmp99SourcePi4ComplexCoarseFineWalkTailScalar anchor sigma choice) •
        cmp99SourcePi4ComplexFineHeadTailWordBase
          K hc hmass hK baseCoarseCovariance head choice
  exact congrArg
    (fun z : ℂ => z • cmp99SourcePi4ComplexFineHeadTailWordBase
      K hc hmass hK baseCoarseCovariance head choice)
    (mul_comm _ _)

/-- Multiplicity retained by the head and the selected tail factors. -/
def cmp99SourcePi4ComplexFineHeadTailMultiplicity
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (selected : Finset (Fin n)) : FinBox 4 (2 * Q) →₀ ℕ :=
  cmp116WeakeningCarrierMultiplicity
      (cmp99SourcePi4FineWalkIndex.active anchor head) +
    cmp116WeakeningFamilyMultiplicity selected fun i =>
      cmp99SourcePi4FineWalkIndex.active anchor (choice i)

/-- Powerset expansion of the exact scalar coefficient.  `omitted` marks
the tail factors contributing `-1`; all remaining carrier occurrences are
retained with multiplicity. -/
theorem cmp99SourcePi4ComplexFineHeadTailScalar_eq_sum_multiplicity
    {M Q R headLength n : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    {layerWord : Fin n → ℕ}
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp99SourcePi4ComplexFineHeadTailScalar anchor sigma head choice =
      ∑ omitted ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : ℂ) ^ omitted.card *
          cmp116ComplexWeakeningMultiplicityMonomial
            (cmp99SourcePi4ComplexFineHeadTailMultiplicity
              anchor head choice (Finset.univ \ omitted)) sigma := by
  unfold cmp99SourcePi4ComplexFineHeadTailScalar
  unfold cmp99SourcePi4ComplexCoarseFineWalkTailScalar
  rw [cmp99OrderedFinProduct_complex_eq_finset_prod]
  rw [prod_cmp116ComplexWeakeningMonomial_sub_one_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omitted homitted
  unfold cmp99SourcePi4ComplexFineHeadTailMultiplicity
  rw [cmp116ComplexWeakeningMonomial_eq_multiplicityMonomial]
  rw [cmp116ComplexWeakeningMultiplicityMonomial_add]
  ring

/-- Complete literal word as a finite sum of multiplicity monomials times
one unchanged ordered physical matrix word. -/
theorem cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_sum_multiplicity
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance sigma head layerWord choice =
      ∑ omitted ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℂ) ^ omitted.card *
          cmp116ComplexWeakeningMultiplicityMonomial
            (cmp99SourcePi4ComplexFineHeadTailMultiplicity
              anchor head choice (Finset.univ \ omitted)) sigma) •
          cmp99SourcePi4ComplexFineHeadTailWordBase
            K hc hmass hK baseCoarseCovariance head choice := by
  rw [cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_smul_base,
    cmp99SourcePi4ComplexFineHeadTailScalar_eq_sum_multiplicity,
    Finset.sum_smul]

end

end YangMills.RG
