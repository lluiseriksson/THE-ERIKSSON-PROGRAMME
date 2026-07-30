/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.FiniteTranslation

/-!
# A volume-independent centering word for local observables

A local observable may use coordinate zero, so a bilateral cluster window
cannot be placed around its original realization.  This module packages a
fixed positive translation word which moves every coordinate by the same
amount.  Finite-volume Gibbs invariance under that word lets later Cauchy
arguments work with the centered observable without changing its
expectation.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace CompatibleLocalObservable

/-- One positive translation in every lattice direction, repeated `r`
times. -/
def centeringWord (d : ℕ) : ℕ → List (Fin d)
  | 0 => []
  | r + 1 => List.ofFn id ++ centeringWord d r

@[simp]
theorem length_centeringWord (d r : ℕ) :
    (centeringWord d r).length = d * r := by
  induction r with
  | zero => simp [centeringWord]
  | succ r ih =>
      rw [centeringWord, List.length_append, List.length_ofFn, ih]
      rw [Nat.mul_succ]
      omega

@[simp]
theorem count_centeringWord {d : ℕ} (r : ℕ) (j : Fin d) :
    (centeringWord d r).count j = r := by
  induction r with
  | zero => simp [centeringWord]
  | succ r ih =>
      have hnodup : (List.ofFn (id : Fin d → Fin d)).Nodup :=
        List.nodup_ofFn.mpr Function.injective_id
      have hj : j ∈ List.ofFn (id : Fin d → Fin d) :=
        List.mem_ofFn.mpr ⟨j, rfl⟩
      rw [centeringWord, List.count_append,
        List.count_eq_one_of_mem hnodup hj, ih]
      omega

/-- Translation preserves the finite support type, although the recursive
definition of `translateList` does not expose that equality definitionally
for a variable word. -/
noncomputable def translateListSupportEquiv
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) :
    (is : List (Fin d)) → (O.translateList is).Support ≃ O.Support
  | [] => Equiv.refl _
  | i :: is => (O.translate i).translateListSupportEquiv is

/-- The source coordinate after an arbitrary translation word is the
original coordinate plus the number of occurrences of that direction. -/
theorem coord_translateList_source
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (is : List (Fin d))
    (s : (O.translateList is).Support) (j : Fin d) :
    (((O.translateList is).coord s).1 j)
      =
    (O.coord (O.translateListSupportEquiv is s)).1 j + is.count j := by
  induction is generalizing O with
  | nil => rfl
  | cons i is ih =>
      change
        ((((O.translate i).translateList is).coord s).1 j)
          =
        (O.coord
            ((O.translate i).translateListSupportEquiv is s)).1 j
          + (i :: is).count j
      rw [ih]
      simp only [translate, List.count_cons]
      by_cases hji : j = i
      · subst j
        simp only [beq_self_eq_true, ite_true]
        omega
      · have hij : i ≠ j := Ne.symm hji
        simp only [beq_iff_eq, hji, hij, ite_false]
        omega

/-- Translation leaves the positive-edge direction of each support
coordinate unchanged. -/
theorem coord_translateList_dir
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (is : List (Fin d))
    (s : (O.translateList is).Support) :
    ((O.translateList is).coord s).2 =
      (O.coord (O.translateListSupportEquiv is s)).2 := by
  induction is generalizing O with
  | nil => rfl
  | cons i is ih =>
      change
        (((O.translate i).translateList is).coord s).2 =
          (O.coord
            ((O.translate i).translateListSupportEquiv is s)).2
      rw [ih]
      rfl

/-- Center an observable by `r` positive units in every coordinate. -/
noncomputable def center
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (r : ℕ) :
    CompatibleLocalObservable d G :=
  O.translateList (centeringWord d r)

/-- Centering only changes support coordinates; it preserves the finite
support cardinality exactly. -/
@[simp]
theorem card_support_center
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (r : ℕ) :
    Fintype.card (O.center r).Support = Fintype.card O.Support := by
  exact Fintype.card_congr
    (O.translateListSupportEquiv (centeringWord d r))

@[simp]
theorem minVolume_center
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (r : ℕ) :
    (O.center r).minVolume = O.minVolume + d * r := by
  simp [center]

@[simp]
theorem coord_centeringWord_source
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (r : ℕ)
    (s : (O.center r).Support) (j : Fin d) :
    (((O.center r).coord s).1 j)
      =
    (O.coord
      (O.translateListSupportEquiv (centeringWord d r) s)).1 j + r := by
  simpa using
    O.coord_translateList_source (centeringWord d r) s j

@[simp]
theorem coord_centeringWord_dir
    {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (r : ℕ)
    (s : (O.center r).Support) :
    ((O.center r).coord s).2
      =
    (O.coord
      (O.translateListSupportEquiv (centeringWord d r) s)).2 := by
  simpa using
    O.coord_translateList_dir (centeringWord d r) s

end CompatibleLocalObservable

/-- Centering does not change a genuine finite-volume Gibbs expectation,
once the enlarged volume guard is satisfied. -/
theorem localGibbsExpectation_center
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (r n : ℕ)
    (hC : (O.center r).minVolume ≤ n) :
    localGibbsExpectation μ pe β (O.center r) n =
      localGibbsExpectation μ pe β O n := by
  exact localGibbsExpectation_translateList
    μ pe β O (CompatibleLocalObservable.centeringWord d r) n hC

end YangMills
