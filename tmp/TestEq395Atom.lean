import YangMills.RG.BalabanCMP99Eq395Algebra
import YangMills.RG.BalabanCMP99PatchedParametrixWalkExpansion

open scoped BigOperators
namespace YangMills.RG

inductive TestSpecies where | first | second | third
deriving DecidableEq, Fintype

def testAtom {Index E : Type*} [Ring E]
    (A : E) (AD chi h C : Index → E) (label : Index × TestSpecies) : E :=
  match label.2 with
  | .first => -cmp99Eq395FirstTerm A (chi label.1) (h label.1) (C label.1)
  | .second => -cmp99Eq395SecondTerm A (AD label.1) (chi label.1) (h label.1) (C label.1)
  | .third => -cmp99Eq395ThirdTerm (AD label.1) (chi label.1) (h label.1) (C label.1)

theorem testSum {Index E : Type*} [Fintype Index] [Ring E]
    (A : E) (AD chi h C : Index → E) :
    (∑ label : Index × TestSpecies, testAtom A AD chi h C label) =
      cmp99Eq395R Finset.univ A AD chi h C := by
  rw [Fintype.sum_prod_type]
  have hspecies (i : Index) :
      (∑ species : TestSpecies, testAtom A AD chi h C (i, species)) =
        -cmp99Eq395FirstTerm A (chi i) (h i) (C i) +
        -cmp99Eq395SecondTerm A (AD i) (chi i) (h i) (C i) +
        -cmp99Eq395ThirdTerm (AD i) (chi i) (h i) (C i) := by
    rw [show (Finset.univ : Finset TestSpecies) =
        {.first, .second, .third} by
      ext species
      cases species <;> simp]
    simp [testAtom]
    abel
  simp only [cmp99Eq395R, cmp99Eq395Correction]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hspecies]
  abel

theorem testPow {Index E : Type*} [Fintype Index] [Ring E]
    (A : E) (AD chi h C : Index → E) (n : ℕ) :
    (cmp99Eq395R Finset.univ A AD chi h C) ^ n =
      ∑ word : Fin n → (Index × TestSpecies),
        cmp99OrderedTupleProduct (testAtom A AD chi h C) word := by
  rw [← testSum]
  exact sum_pow_eq_sum_cmp99OrderedTupleProduct _ n

end YangMills.RG
