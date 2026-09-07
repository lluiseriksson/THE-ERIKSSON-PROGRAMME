/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexFineHeadTailWordExpansion

/-!
# Exact weakening support of literal complex CMP99 walk terms

Every fully refined minimizer summand depends only on the union of the
weakening carriers of its literal head and tail walks.  This module proves
that source-locality statement directly, rather than attaching an abstract
support certificate after the fact.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Pointwise equality of factors preserves their dependent ordered
product. -/
theorem cmp99DependentOrderedProduct_congr
    {E : Type*} [Monoid E] {n : ℕ}
    {α : Fin n → Type*}
    (R S : ∀ i, α i → E) (choice : ∀ i, α i)
    (h : ∀ i, R i (choice i) = S i (choice i)) :
    cmp99DependentOrderedProduct R choice =
      cmp99DependentOrderedProduct S choice := by
  unfold cmp99DependentOrderedProduct cmp99OrderedFinProduct
  apply congrArg List.prod
  apply (List.ofFn_inj).2
  funext i
  exact h i

/-- A complex weakening monomial only reads its active coordinates. -/
theorem cmp116ComplexWeakeningMonomial_eq_of_eqOn
    {D : Type*} [DecidableEq D]
    (active : Finset D) (sigma tau : D → ℂ)
    (h : ∀ d ∈ active, sigma d = tau d) :
    cmp116ComplexWeakeningMonomial active sigma =
      cmp116ComplexWeakeningMonomial active tau := by
  unfold cmp116ComplexWeakeningMonomial
  apply Finset.prod_congr rfl
  intro d hd
  exact h d hd

/-- One literal fine-walk matrix depends only on that walk's exact source
carrier. -/
theorem cmp99SourcePi4ComplexFineWalkTerm_eq_of_eqOn_active
    {M Q Nc R walkLength : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma tau : FinBox 4 (2 * Q) → ℂ)
    (index : CMP99SourcePi4FineWalkIndex M Q R walkLength)
    (h : ∀ d ∈ cmp99SourcePi4FineWalkIndex.active anchor index,
      sigma d = tau d) :
    cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK sigma index =
      cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK tau index := by
  unfold cmp99SourcePi4ComplexFineWalkTerm
  rw [cmp116ComplexWeakeningMonomial_eq_of_eqOn _ sigma tau h]

/-- A transported fine-walk defect has the same exact weakening support as
its underlying walk. -/
theorem
    cmp99SourcePi4ComplexCoarseFineWalkDefectTerm_eq_of_eqOn_active
    {M Q Nc R walkLength : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma tau : FinBox 4 (2 * Q) → ℂ)
    (index : CMP99SourcePi4FineWalkIndex M Q R walkLength)
    (h : ∀ d ∈ cmp99SourcePi4FineWalkIndex.active anchor index,
      sigma d = tau d) :
    cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
        anchor K hc hmass hK baseCoarseCovariance sigma index =
      cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
        anchor K hc hmass hK baseCoarseCovariance tau index := by
  unfold cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
  rw [cmp99SourcePi4ComplexFineWalkTerm_eq_of_eqOn_active
    anchor K hc hmass hK sigma tau index h]

/-- The ordered tail word reads exactly the union of the carriers of its
chosen physical walks. -/
theorem
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm_eq_of_eqOn_active
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma tau : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (h : ∀ d ∈
      cmp99SourcePi4CoarseFineWalkChoiceActive anchor choice,
      sigma d = tau d) :
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice =
      cmp99SourcePi4ComplexCoarseFineWalkWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        tau layerWord choice := by
  unfold cmp99SourcePi4ComplexCoarseFineWalkWordTerm
  apply cmp99DependentOrderedProduct_congr
  intro i
  rw [
    cmp99SourcePi4ComplexCoarseFineWalkDefectTerm_eq_of_eqOn_active
      anchor K hc hmass hK baseCoarseCovariance
      sigma tau (choice i) (fun d hd => h d
        ((mem_cmp99SourcePi4CoarseFineWalkChoiceActive_iff
          anchor choice d).2 ⟨i, hd⟩))]

/-- A completely literal head-tail minimizer term depends only on its
explicit total carrier. -/
theorem
    cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_of_eqOn_active
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma tau : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (h : ∀ d ∈ cmp99SourcePi4FineHeadTailActive
      anchor head choice, sigma d = tau d) :
    cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice =
      cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        tau head layerWord choice := by
  unfold cmp99SourcePi4ComplexFineHeadTailWordTerm
  rw [cmp99SourcePi4ComplexFineWalkTerm_eq_of_eqOn_active
    anchor K hc hmass hK sigma tau head
    (fun d hd => h d (by
      exact Finset.mem_union_left _ hd))]
  rw [
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm_eq_of_eqOn_active
      anchor K hc hmass hK baseCoarseCovariance
      sigma tau layerWord choice
      (fun d hd => h d (by
        exact Finset.mem_union_right _ hd))]

end

end YangMills.RG
