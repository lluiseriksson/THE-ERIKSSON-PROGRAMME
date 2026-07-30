/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalObservableSubstrate

/-!
# Algebraic operations on compatible local observables

The original substrate deliberately carried individual observables only.  This
module supplies the finite-support union needed to add two observables without
duplicating a coordinate, together with scalar multiplication and their exact
finite-volume realization identities.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace CompatibleLocalObservable

open Classical

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- The finite set of volume-independent positive-edge coordinates read by an
observable. -/
noncomputable def coordinateFinset (O : CompatibleLocalObservable d G) :
    Finset ((Fin d → ℕ) × Fin d) :=
  Finset.univ.image O.coord

@[simp]
theorem coord_mem_coordinateFinset
    (O : CompatibleLocalObservable d G) (s : O.Support) :
    O.coord s ∈ O.coordinateFinset := by
  simp [coordinateFinset]

/-- Coordinate support of a sum, with overlaps represented only once. -/
noncomputable def addCoordinateFinset
    (O P : CompatibleLocalObservable d G) :
    Finset ((Fin d → ℕ) × Fin d) :=
  O.coordinateFinset ∪ P.coordinateFinset

/-- Assignment on the union support restricted back to the left support. -/
noncomputable def addLeftAssignment
    (O P : CompatibleLocalObservable d G)
    (x : {c // c ∈ addCoordinateFinset O P} → G) :
    O.Support → G :=
  fun s => x ⟨O.coord s, Finset.mem_union_left _
    (O.coord_mem_coordinateFinset s)⟩

/-- Assignment on the union support restricted back to the right support. -/
noncomputable def addRightAssignment
    (O P : CompatibleLocalObservable d G)
    (x : {c // c ∈ addCoordinateFinset O P} → G) :
    P.Support → G :=
  fun s => x ⟨P.coord s, Finset.mem_union_right _
    (P.coord_mem_coordinateFinset s)⟩

theorem measurable_addLeftAssignment
    (O P : CompatibleLocalObservable d G) :
    Measurable (addLeftAssignment O P) := by
  apply measurable_pi_lambda
  intro s
  exact measurable_pi_apply _

theorem measurable_addRightAssignment
    (O P : CompatibleLocalObservable d G) :
    Measurable (addRightAssignment O P) := by
  apply measurable_pi_lambda
  intro s
  exact measurable_pi_apply _

/-- Sum of two local observables on the union of their coordinate supports. -/
noncomputable def add
    (O P : CompatibleLocalObservable d G) :
    CompatibleLocalObservable d G where
  Support := {c // c ∈ addCoordinateFinset O P}
  coord := fun c => c.1
  coord_injective := Subtype.val_injective
  minVolume := max O.minVolume P.minVolume
  coord_lt := by
    intro c j
    rcases Finset.mem_union.mp c.2 with hc | hc
    · rcases Finset.mem_image.mp hc with ⟨s, -, hs⟩
      rw [← hs]
      exact (O.coord_lt s j).trans_le
        (Nat.add_le_add_right (le_max_left _ _) 1)
    · rcases Finset.mem_image.mp hc with ⟨s, -, hs⟩
      rw [← hs]
      exact (P.coord_lt s j).trans_le
        (Nat.add_le_add_right (le_max_right _ _) 1)
  kernel := fun x =>
    O.kernel (addLeftAssignment O P x) +
      P.kernel (addRightAssignment O P x)
  kernel_measurable :=
    (O.kernel_measurable.comp (measurable_addLeftAssignment O P)).add
      (P.kernel_measurable.comp (measurable_addRightAssignment O P))
  bound := O.bound + P.bound
  bound_nonneg := add_nonneg O.bound_nonneg P.bound_nonneg
  kernel_bound := by
    intro x
    exact (abs_add_le _ _).trans
      (add_le_add (O.kernel_bound _) (P.kernel_bound _))

/-- Product of two local observables on the union of their coordinate
supports.  Using the same deduplicated union as `add` is essential when the
two observables read a common edge. -/
noncomputable def mul
    (O P : CompatibleLocalObservable d G) :
    CompatibleLocalObservable d G where
  Support := {c // c ∈ addCoordinateFinset O P}
  coord := fun c => c.1
  coord_injective := Subtype.val_injective
  minVolume := max O.minVolume P.minVolume
  coord_lt := by
    intro c j
    rcases Finset.mem_union.mp c.2 with hc | hc
    · rcases Finset.mem_image.mp hc with ⟨s, -, hs⟩
      rw [← hs]
      exact (O.coord_lt s j).trans_le
        (Nat.add_le_add_right (le_max_left _ _) 1)
    · rcases Finset.mem_image.mp hc with ⟨s, -, hs⟩
      rw [← hs]
      exact (P.coord_lt s j).trans_le
        (Nat.add_le_add_right (le_max_right _ _) 1)
  kernel := fun x =>
    O.kernel (addLeftAssignment O P x) *
      P.kernel (addRightAssignment O P x)
  kernel_measurable :=
    (O.kernel_measurable.comp (measurable_addLeftAssignment O P)).mul
      (P.kernel_measurable.comp (measurable_addRightAssignment O P))
  bound := O.bound * P.bound
  bound_nonneg := mul_nonneg O.bound_nonneg P.bound_nonneg
  kernel_bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (O.kernel_bound _) (P.kernel_bound _)
      (abs_nonneg _) O.bound_nonneg

/-- Scalar multiple of a compatible local observable. -/
noncomputable def smul
    (c : ℝ) (O : CompatibleLocalObservable d G) :
    CompatibleLocalObservable d G where
  Support := O.Support
  coord := O.coord
  coord_injective := O.coord_injective
  minVolume := O.minVolume
  coord_lt := O.coord_lt
  kernel := fun x => c * O.kernel x
  kernel_measurable := measurable_const.mul O.kernel_measurable
  bound := |c| * O.bound
  bound_nonneg := mul_nonneg (abs_nonneg _) O.bound_nonneg
  kernel_bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (O.kernel_bound _) (abs_nonneg _)

@[simp]
theorem minVolume_add
    (O P : CompatibleLocalObservable d G) :
    (add O P).minVolume = max O.minVolume P.minVolume := rfl

@[simp]
theorem minVolume_mul
    (O P : CompatibleLocalObservable d G) :
    (mul O P).minVolume = max O.minVolume P.minVolume := rfl

@[simp]
theorem minVolume_smul
    (c : ℝ) (O : CompatibleLocalObservable d G) :
    (smul c O).minVolume = O.minVolume := rfl

/-- Exact realization of a sum at every jointly admissible volume. -/
theorem realize_add
    (O P : CompatibleLocalObservable d G)
    (n : ℕ) (h : max O.minVolume P.minVolume ≤ n)
    (A : GaugeConfig d (n + 1) G) :
    (add O P).realize n A = O.realize n A + P.realize n A := by
  have hO : O.minVolume ≤ n := (le_max_left _ _).trans h
  have hP : P.minVolume ≤ n := (le_max_right _ _).trans h
  simp only [CompatibleLocalObservable.realize, dif_pos h, dif_pos hO,
    dif_pos hP, add, addLeftAssignment, addRightAssignment]
  rfl

/-- Exact realization of a product at every jointly admissible volume. -/
theorem realize_mul
    (O P : CompatibleLocalObservable d G)
    (n : ℕ) (h : max O.minVolume P.minVolume ≤ n)
    (A : GaugeConfig d (n + 1) G) :
    (mul O P).realize n A = O.realize n A * P.realize n A := by
  have hO : O.minVolume ≤ n := (le_max_left _ _).trans h
  have hP : P.minVolume ≤ n := (le_max_right _ _).trans h
  simp only [CompatibleLocalObservable.realize, dif_pos h, dif_pos hO,
    dif_pos hP, mul, addLeftAssignment, addRightAssignment]
  rfl

/-- Exact realization of a scalar multiple. -/
theorem realize_smul
    (c : ℝ) (O : CompatibleLocalObservable d G)
    (n : ℕ) (h : O.minVolume ≤ n)
    (A : GaugeConfig d (n + 1) G) :
    (smul c O).realize n A = c * O.realize n A := by
  have hS : (smul c O).minVolume ≤ n := by
    simpa using h
  rw [CompatibleLocalObservable.realize, dif_pos hS,
    CompatibleLocalObservable.realize, dif_pos h]
  change c * O.kernel _ = c * O.kernel _
  congr 1

end CompatibleLocalObservable

section FiniteAlgebra

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableMul₂ G] [MeasurableInv G]

/-- Finite-volume linearity for the coordinate-union sum. -/
theorem localGibbsExpectation_add
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O P : CompatibleLocalObservable d G)
    (n : ℕ) (h : max O.minVolume P.minVolume ≤ n) :
    localGibbsExpectation μ pe β
        (CompatibleLocalObservable.add O P) n =
      localGibbsExpectation μ pe β O n +
        localGibbsExpectation μ pe β P n := by
  unfold localGibbsExpectation
  rw [show
    (CompatibleLocalObservable.add O P).realize n =
      fun A => O.realize n A + P.realize n A by
        funext A
        exact CompatibleLocalObservable.realize_add O P n h A]
  exact expectation_add d (n + 1) μ pe β
    (integrable_realize_gibbs μ hpe_meas hpe β O n)
    (integrable_realize_gibbs μ hpe_meas hpe β P n)

/-- Finite-volume real scalar linearity. -/
theorem localGibbsExpectation_smul
    (μ : Measure G)
    (pe : G → ℝ) (β c : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) :
    localGibbsExpectation μ pe β
        (CompatibleLocalObservable.smul c O) n =
      c * localGibbsExpectation μ pe β O n := by
  unfold localGibbsExpectation expectation
  rw [show
    (CompatibleLocalObservable.smul c O).realize n =
      fun A => c * O.realize n A by
        funext A
        exact CompatibleLocalObservable.realize_smul c O n h A]
  exact integral_const_mul c (O.realize n)

end FiniteAlgebra

end YangMills
