/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexFineWalkLayerExpansion

/-!
# Dependent fine-walk expansion of coarse CMP99 words

The layer at each position of a coarse word has its own finite type of
physical walks.  This module proves the required dependent distributivity
without using `Finset.prod`: all operator products remain ordered and
noncommutative.
-/

namespace YangMills.RG

noncomputable section

universe u v

/-- Ordered product of a `Fin`-indexed family. -/
def cmp99OrderedFinProduct
    {E : Type v} [Monoid E] {n : ℕ} (f : Fin n → E) : E :=
  (List.ofFn f).prod

@[simp]
theorem cmp99OrderedFinProduct_zero
    {E : Type v} [Monoid E] (f : Fin 0 → E) :
    cmp99OrderedFinProduct f = 1 := by
  simp [cmp99OrderedFinProduct]

/-- The first coordinate is the leftmost factor. -/
theorem cmp99OrderedFinProduct_succ
    {E : Type v} [Monoid E] {n : ℕ}
    (f : Fin (n + 1) → E) :
    cmp99OrderedFinProduct f =
      f 0 * cmp99OrderedFinProduct (fun i => f i.succ) := by
  simp only [cmp99OrderedFinProduct, List.ofFn_succ, List.prod_cons]

/-- Ordered product after choosing one value from each dependent fiber. -/
def cmp99DependentOrderedProduct
    {E : Type v} [Monoid E] {n : ℕ}
    {α : Fin n → Type u}
    (R : ∀ i, α i → E)
    (choice : ∀ i, α i) : E :=
  cmp99OrderedFinProduct (fun i => R i (choice i))

/-- Noncommutative dependent distributivity: an ordered product of finite
sums is the finite sum over dependent choices of the ordered products. -/
theorem cmp99OrderedFinProduct_sum_eq_sum_dependent
    {E : Type v} [Semiring E] :
    ∀ {n : ℕ} (α : Fin n → Type u)
      [∀ i, Fintype (α i)]
      (R : ∀ i, α i → E),
      cmp99OrderedFinProduct (fun i => ∑ x : α i, R i x) =
        ∑ choice : ∀ i, α i,
          cmp99DependentOrderedProduct R choice := by
  intro n
  induction n with
  | zero =>
      intro α _ R
      simp [cmp99DependentOrderedProduct]
  | succ n ih =>
      intro α _ R
      have hhead :
          ∀ (x : α 0) (tail : ∀ i : Fin n, α i.succ),
            cmp99DependentOrderedProduct R (Fin.cons x tail) =
              R 0 x *
                cmp99DependentOrderedProduct
                  (fun i value => R i.succ value) tail := by
        intro x tail
        rw [cmp99DependentOrderedProduct,
          cmp99OrderedFinProduct_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rfl
      symm
      calc
        (∑ choice : ∀ i : Fin (n + 1), α i,
            cmp99DependentOrderedProduct R choice) =
          ∑ pair : α 0 × (∀ i : Fin n, α i.succ),
            cmp99DependentOrderedProduct R
              (Fin.cons pair.1 pair.2) := by
          exact
            (Fintype.sum_equiv
              (Fin.consEquiv α)
              (fun pair =>
                cmp99DependentOrderedProduct R
                  (Fin.cons pair.1 pair.2))
              (fun choice =>
                cmp99DependentOrderedProduct R choice)
              (fun _ => rfl)).symm
        _ = ∑ x : α 0, ∑ tail : ∀ i : Fin n, α i.succ,
            cmp99DependentOrderedProduct R (Fin.cons x tail) :=
          Fintype.sum_prod_type _
        _ = ∑ x : α 0, ∑ tail : ∀ i : Fin n, α i.succ,
            R 0 x *
              cmp99DependentOrderedProduct
                (fun i value => R i.succ value) tail := by
          apply Finset.sum_congr rfl
          intro x _hx
          apply Finset.sum_congr rfl
          intro tail _htail
          exact hhead x tail
        _ = (∑ x : α 0, R 0 x) *
            ∑ tail : ∀ i : Fin n, α i.succ,
              cmp99DependentOrderedProduct
                (fun i value => R i.succ value) tail := by
          exact
            (Finset.sum_mul_sum Finset.univ Finset.univ
              (fun x => R 0 x)
              (fun tail =>
                cmp99DependentOrderedProduct
                  (fun i value => R i.succ value) tail)).symm
        _ = (∑ x : α 0, R 0 x) *
            cmp99OrderedFinProduct
              (fun i : Fin n => ∑ x : α i.succ, R i.succ x) := by
          rw [ih (fun i => α i.succ)
            (fun i value => R i.succ value)]
        _ = cmp99OrderedFinProduct
            (fun i : Fin (n + 1) => ∑ x : α i, R i x) :=
          (cmp99OrderedFinProduct_succ
            (fun i : Fin (n + 1) => ∑ x : α i, R i x)).symm

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- A dependent choice of one literal fine walk at every position of a
coarse layer word. -/
abbrev CMP99SourcePi4CoarseFineWalkChoice
    (M Q R : ℕ) {n : ℕ} (layerWord : Fin n → ℕ)
    [NeZero M] [NeZero Q] :=
  ∀ i, CMP99SourcePi4FineWalkIndex M Q R (layerWord i)

/-- Ordered product of the literal fine-walk defect terms chosen below one
coarse layer word. -/
noncomputable def cmp99SourcePi4ComplexCoarseFineWalkWordTerm
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
    (choice : CMP99SourcePi4CoarseFineWalkChoice
      M Q R layerWord) :=
  cmp99DependentOrderedProduct
    (fun i index =>
      -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
        anchor K hc hmass hK baseCoarseCovariance sigma index)
    choice

/-- Negating one coarse layer distributes over its finite physical
fine-walk decomposition. -/
theorem
    neg_cmp99SourcePi4ComplexCoarseRelativeDefectLayer_eq_sum_fineWalkTerms
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
    (layer : ℕ) :
    -cmp99SourcePi4ComplexCoarseRelativeDefectLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma layer =
      ∑ index : CMP99SourcePi4FineWalkIndex M Q R layer,
        -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
          anchor K hc hmass hK baseCoarseCovariance sigma index := by
  rw [
    cmp99SourcePi4ComplexCoarseRelativeDefectLayer_eq_sum_fineWalkTerms]
  change
    -(Finset.univ.sum fun index =>
        cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
          anchor K hc hmass hK baseCoarseCovariance sigma index) =
      Finset.univ.sum fun index =>
        -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
          anchor K hc hmass hK baseCoarseCovariance sigma index
  exact (Finset.sum_neg_distrib _).symm

/-- A coarse ordered word is exactly the finite sum over dependent choices
of its literal fine walks.  No operator factors are commuted. -/
theorem
    cmp99OrderedCoarseRelativeDefectWord_eq_sum_fineWalkChoices
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
    (layerWord : Fin n → ℕ) :
    cmp99OrderedTupleProduct
        (fun layer : ℕ =>
          -cmp99SourcePi4ComplexCoarseRelativeDefectLayer
            (R := R) anchor K hc hmass hK
            baseCoarseCovariance sigma layer)
        layerWord =
      ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp99SourcePi4ComplexCoarseFineWalkWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice := by
  let coarseLayer := fun layer : ℕ =>
    cmp99SourcePi4ComplexCoarseRelativeDefectLayer
      (R := R) anchor K hc hmass hK
      baseCoarseCovariance sigma layer
  let fineTerm := fun (i : Fin n)
      (index : CMP99SourcePi4FineWalkIndex M Q R (layerWord i)) =>
    -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
      anchor K hc hmass hK baseCoarseCovariance sigma index
  calc
    cmp99OrderedTupleProduct
        (fun layer : ℕ => -coarseLayer layer) layerWord =
      cmp99OrderedFinProduct
        (fun i : Fin n => -coarseLayer (layerWord i)) := by
      unfold cmp99OrderedTupleProduct cmp99OrderedFinProduct
      rw [List.map_ofFn]
      apply congrArg List.prod
      exact (List.ofFn_inj).2 (by funext _; rfl)
    _ = cmp99OrderedFinProduct
        (fun i : Fin n =>
          ∑ index : CMP99SourcePi4FineWalkIndex
              M Q R (layerWord i),
            fineTerm i index) := by
      congr 1
      funext i
      exact
        neg_cmp99SourcePi4ComplexCoarseRelativeDefectLayer_eq_sum_fineWalkTerms
          anchor K hc hmass hK baseCoarseCovariance sigma (layerWord i)
    _ = ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp99DependentOrderedProduct fineTerm choice :=
      cmp99OrderedFinProduct_sum_eq_sum_dependent
        (fun i : Fin n =>
          CMP99SourcePi4FineWalkIndex M Q R (layerWord i))
        fineTerm
    _ = ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        cmp99SourcePi4ComplexCoarseFineWalkWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice := by
      apply Finset.sum_congr rfl
      intro choice _hchoice
      rfl

end

end YangMills.RG
