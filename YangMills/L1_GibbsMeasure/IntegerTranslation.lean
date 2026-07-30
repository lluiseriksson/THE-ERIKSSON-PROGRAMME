/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.ThermodynamicLimit

/-!
# The full integer translation action on local Gibbs observables

`CompatibleLocalObservable` uses natural-number coordinates.  That chart is
ideal for a one-sided thermodynamic exhaustion, but its positive translation
is not surjective: an observable with a coordinate at zero has no negative
translate in the same type.  Consequently it cannot honestly carry the full
translation-group action.

This module supplies the missing intrinsic chart.  `IntegerLocalObservable`
has finite support in `ℤ^d`, is realized on every periodic torus by Euclidean
reduction `Int.natMod`, and carries the genuine additive action of
`Fin d → ℤ`.  Its finite-volume value is again the literal normalized Gibbs
integral.

For convergence, every integer-coordinate observable is shifted by one fixed
finite vector into the natural chart.  Its finite Gibbs expectation is
unchanged by that shift, and from an explicit volume onward its realization
is exactly the realization of a `CompatibleLocalObservable`.  Thus the
already-proved whole-sequence KP theorem applies without compactness or a
subsequence.

The terminal object `TranslationInvariantLocalState` is positive, normalized,
real linear, and invariant under every `z : Fin d → ℤ`.  The `AddAction` laws
are proved on the observable type itself, so inverse translations are literal
group inverses rather than volume-dependent positive words.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open Filter MeasureTheory GaugeConfig
open scoped BigOperators Topology

/-- A bounded measurable local observable whose absolute edge coordinates
live in the universal cover `ℤ^d`. -/
structure IntegerLocalObservable
    (d : ℕ) [NeZero d]
    (G : Type*) [Group G] [MeasurableSpace G] where
  Support : Type*
  [supportFintype : Fintype Support]
  coord : Support → (Fin d → ℤ) × Fin d
  coord_injective : Function.Injective coord
  kernel : (Support → G) → ℝ
  kernel_measurable : Measurable kernel
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  kernel_bound : ∀ x, |kernel x| ≤ bound

attribute [instance] IntegerLocalObservable.supportFintype

namespace IntegerLocalObservable

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Reduction of an integer source coordinate into the side-`n+1` torus. -/
def edgeAt (O : IntegerLocalObservable d G) (n : ℕ)
    (s : O.Support) : PosEdge d (n + 1) :=
  ⟨⟨fun j =>
      ⟨(O.coord s).1 j |>.natMod (n + 1),
        Int.natMod_lt (Nat.succ_ne_zero n)⟩,
    (O.coord s).2, true⟩, rfl⟩

/-- Restriction of a torus gauge configuration to the integer-coordinate
support.  Different universal-cover coordinates may coincide in a small
torus; that is the genuine periodic realization, not an undersized zero
branch. -/
noncomputable def restrictConfig
    (O : IntegerLocalObservable d G) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) : O.Support → G :=
  fun s => configToPos A (O.edgeAt n s)

/-- Genuine periodic realization of an integer-coordinate local observable. -/
noncomputable def realize
    (O : IntegerLocalObservable d G) (n : ℕ) :
    GaugeConfig d (n + 1) G → ℝ :=
  fun A => O.kernel (O.restrictConfig n A)

theorem measurable_realize
    (O : IntegerLocalObservable d G) (n : ℕ) :
    Measurable (O.realize n) := by
  apply O.kernel_measurable.comp
  apply measurable_pi_lambda
  intro s
  exact (measurable_pi_apply (O.edgeAt n s)).comp
    (gaugeConfigMEquiv (d := d) (N := n + 1) (G := G)).symm.measurable

theorem abs_realize_le
    (O : IntegerLocalObservable d G) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    |O.realize n A| ≤ O.bound :=
  O.kernel_bound _

/-- Constants are integer-coordinate local observables with empty support. -/
noncomputable def const (c : ℝ) : IntegerLocalObservable d G where
  Support := Fin 0
  coord := fun i => Fin.elim0 i
  coord_injective := fun i => Fin.elim0 i
  kernel := fun _ => c
  kernel_measurable := measurable_const
  bound := |c|
  bound_nonneg := abs_nonneg c
  kernel_bound := fun _ => le_rfl

@[simp]
theorem realize_const (c : ℝ) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    (const (d := d) (G := G) c).realize n A = c := by
  rfl

/-- Translation of all universal-cover coordinates by `z`. -/
def translate
    (z : Fin d → ℤ) (O : IntegerLocalObservable d G) :
    IntegerLocalObservable d G where
  Support := O.Support
  coord := fun s =>
    ⟨fun j => (O.coord s).1 j + z j, (O.coord s).2⟩
  coord_injective := by
    intro s t hst
    apply O.coord_injective
    apply Prod.ext
    · funext j
      have hj := congrArg (fun c => c.1 j) hst
      dsimp at hj
      omega
    · have hdir := congrArg Prod.snd hst
      simpa using hdir
  kernel := O.kernel
  kernel_measurable := O.kernel_measurable
  bound := O.bound
  bound_nonneg := O.bound_nonneg
  kernel_bound := O.kernel_bound

instance : VAdd (Fin d → ℤ) (IntegerLocalObservable d G) :=
  ⟨translate⟩

@[simp]
theorem zero_vadd (O : IntegerLocalObservable d G) :
    (0 : Fin d → ℤ) +ᵥ O = O := by
  change translate 0 O = O
  cases O
  simp [translate]

theorem add_vadd (z w : Fin d → ℤ)
    (O : IntegerLocalObservable d G) :
    (z + w) +ᵥ O = z +ᵥ (w +ᵥ O) := by
  change translate (z + w) O = translate z (translate w O)
  cases O
  simp [translate, add_assoc, add_comm]

instance : AddAction (Fin d → ℤ) (IntegerLocalObservable d G) where
  zero_vadd := zero_vadd
  add_vadd := add_vadd

/-- Negative translation is a literal inverse in the observable type. -/
@[simp]
theorem neg_vadd_vadd (z : Fin d → ℤ)
    (O : IntegerLocalObservable d G) :
    (-z) +ᵥ (z +ᵥ O) = O := by
  calc
    (-z) +ᵥ (z +ᵥ O) = ((-z) + z) +ᵥ O :=
      (add_vadd (-z) z O).symm
    _ = O := by simp

@[simp]
theorem coord_vadd (z : Fin d → ℤ)
    (O : IntegerLocalObservable d G) (s : O.Support) :
    ((z +ᵥ O).coord s).1 = fun j => (O.coord s).1 j + z j :=
  rfl

/-- The positive unit vector in direction `i`. -/
def unitVector (i : Fin d) : Fin d → ℤ :=
  Pi.single i 1

/-- The negative unit vector in direction `i`. -/
def negUnitVector (i : Fin d) : Fin d → ℤ :=
  Pi.single i (-1)

/-! ## Exact finite-volume algebra -/

open Classical

noncomputable def coordinateFinset (O : IntegerLocalObservable d G) :
    Finset ((Fin d → ℤ) × Fin d) :=
  Finset.univ.image O.coord

@[simp]
theorem coord_mem_coordinateFinset
    (O : IntegerLocalObservable d G) (s : O.Support) :
    O.coord s ∈ O.coordinateFinset := by
  simp [coordinateFinset]

noncomputable def addCoordinateFinset
    (O P : IntegerLocalObservable d G) :
    Finset ((Fin d → ℤ) × Fin d) :=
  O.coordinateFinset ∪ P.coordinateFinset

noncomputable def addLeftAssignment
    (O P : IntegerLocalObservable d G)
    (x : {c // c ∈ addCoordinateFinset O P} → G) :
    O.Support → G :=
  fun s => x ⟨O.coord s, Finset.mem_union_left _
    (O.coord_mem_coordinateFinset s)⟩

noncomputable def addRightAssignment
    (O P : IntegerLocalObservable d G)
    (x : {c // c ∈ addCoordinateFinset O P} → G) :
    P.Support → G :=
  fun s => x ⟨P.coord s, Finset.mem_union_right _
    (P.coord_mem_coordinateFinset s)⟩

theorem measurable_addLeftAssignment
    (O P : IntegerLocalObservable d G) :
    Measurable (addLeftAssignment O P) := by
  apply measurable_pi_lambda
  intro s
  exact measurable_pi_apply _

theorem measurable_addRightAssignment
    (O P : IntegerLocalObservable d G) :
    Measurable (addRightAssignment O P) := by
  apply measurable_pi_lambda
  intro s
  exact measurable_pi_apply _

noncomputable def add
    (O P : IntegerLocalObservable d G) :
    IntegerLocalObservable d G where
  Support := {c // c ∈ addCoordinateFinset O P}
  coord := fun c => c.1
  coord_injective := Subtype.val_injective
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

noncomputable def mul
    (O P : IntegerLocalObservable d G) :
    IntegerLocalObservable d G where
  Support := {c // c ∈ addCoordinateFinset O P}
  coord := fun c => c.1
  coord_injective := Subtype.val_injective
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

noncomputable def smul
    (c : ℝ) (O : IntegerLocalObservable d G) :
    IntegerLocalObservable d G where
  Support := O.Support
  coord := O.coord
  coord_injective := O.coord_injective
  kernel := fun x => c * O.kernel x
  kernel_measurable := measurable_const.mul O.kernel_measurable
  bound := |c| * O.bound
  bound_nonneg := mul_nonneg (abs_nonneg _) O.bound_nonneg
  kernel_bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (O.kernel_bound _) (abs_nonneg _)

theorem realize_add
    (O P : IntegerLocalObservable d G) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    (add O P).realize n A = O.realize n A + P.realize n A := by
  rfl

theorem realize_mul
    (O P : IntegerLocalObservable d G) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    (mul O P).realize n A = O.realize n A * P.realize n A := by
  rfl

theorem realize_smul
    (c : ℝ) (O : IntegerLocalObservable d G) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    (smul c O).realize n A = c * O.realize n A := by
  rfl

/-! ## A canonical natural-coordinate chart -/

/-- A coordinatewise positive shift large enough to move the whole finite
support into `ℕ^d`. -/
noncomputable def lowerShift
    (O : IntegerLocalObservable d G) (j : Fin d) : ℕ :=
  (Finset.univ : Finset O.Support).sup
    (fun s => Int.toNat (-(O.coord s).1 j))

theorem coord_add_lowerShift_nonneg
    (O : IntegerLocalObservable d G) (s : O.Support) (j : Fin d) :
    0 ≤ (O.coord s).1 j + (O.lowerShift j : ℤ) := by
  have hle :
      Int.toNat (-(O.coord s).1 j) ≤ O.lowerShift j := by
    exact Finset.le_sup (f :=
      fun s : O.Support => Int.toNat (-(O.coord s).1 j))
      (Finset.mem_univ s)
  omega

noncomputable def natCoord
    (O : IntegerLocalObservable d G) (s : O.Support) (j : Fin d) : ℕ :=
  Int.toNat ((O.coord s).1 j + (O.lowerShift j : ℤ))

noncomputable def coordinateBound
    (O : IntegerLocalObservable d G) : ℕ :=
  (Finset.univ : Finset O.Support).sup
    (fun s => (Finset.univ : Finset (Fin d)).sup (O.natCoord s))

/-- The canonical natural-coordinate representative of an integer local
observable, obtained by one common coordinatewise translation. -/
noncomputable def toCompatible
    (O : IntegerLocalObservable d G) :
    CompatibleLocalObservable d G where
  Support := O.Support
  coord := fun s => ⟨O.natCoord s, (O.coord s).2⟩
  coord_injective := by
    intro s t hst
    apply O.coord_injective
    apply Prod.ext
    · funext j
      have hj := congrArg (fun c => c.1 j) hst
      simp only at hj
      have hs := O.coord_add_lowerShift_nonneg s j
      have ht := O.coord_add_lowerShift_nonneg t j
      simp only [natCoord] at hj
      have :
          (O.coord s).1 j + (O.lowerShift j : ℤ) =
            (O.coord t).1 j + (O.lowerShift j : ℤ) := by
        omega
      omega
    · have hdir := congrArg Prod.snd hst
      simpa using hdir
  minVolume := O.coordinateBound
  coord_lt := by
    intro s j
    have hj :
        O.natCoord s j ≤
          (Finset.univ : Finset (Fin d)).sup (O.natCoord s) :=
      Finset.le_sup (f := O.natCoord s) (Finset.mem_univ j)
    have hs :
        (Finset.univ : Finset (Fin d)).sup (O.natCoord s) ≤
          O.coordinateBound := by
      exact Finset.le_sup (f := fun s : O.Support =>
        (Finset.univ : Finset (Fin d)).sup (O.natCoord s))
        (Finset.mem_univ s)
    exact (hj.trans hs).trans_lt (Nat.lt_succ_self _)
  kernel := O.kernel
  kernel_measurable := O.kernel_measurable
  bound := O.bound
  bound_nonneg := O.bound_nonneg
  kernel_bound := O.kernel_bound

/-- The integer vector underlying the canonical positive chart shift. -/
noncomputable def lowerShiftVector
    (O : IntegerLocalObservable d G) : Fin d → ℤ :=
  fun j => O.lowerShift j

end IntegerLocalObservable

/-! ## Genuine finite Gibbs expectations and unit translations -/

section IntegerExpectation

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableMul₂ G] [MeasurableInv G]

/-- Literal finite-volume Gibbs expectation of an integer-coordinate local
observable. -/
noncomputable def integerLocalGibbsExpectation
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (n : ℕ) : ℝ :=
  expectation d (n + 1) μ pe β (O.realize n)

theorem integrable_integerRealize_gibbs
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : IntegerLocalObservable d G) (n : ℕ) :
    Integrable (O.realize n)
      (gibbsMeasure (d := d) (N := n + 1) μ pe β) := by
  letI : IsProbabilityMeasure
      (gibbsMeasure (d := d) (N := n + 1) μ pe β) :=
    gibbsMeasure_isProbability' μ hpe_meas hpe β
  refine (integrable_const O.bound).mono'
    (O.measurable_realize n).aestronglyMeasurable ?_
  exact ae_of_all _ fun A => by
    simpa [Real.norm_eq_abs] using O.abs_realize_le n A

theorem integerLocalGibbsExpectation_nonneg
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (n : ℕ)
    (hO : ∀ x, 0 ≤ O.kernel x) :
    0 ≤ integerLocalGibbsExpectation μ pe β O n := by
  unfold integerLocalGibbsExpectation expectation
  exact integral_nonneg fun A => hO _

theorem integerLocalGibbsExpectation_const
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β c : ℝ) (n : ℕ) :
    integerLocalGibbsExpectation μ pe β
      (IntegerLocalObservable.const (d := d) (G := G) c) n = c := by
  unfold integerLocalGibbsExpectation
  simpa using expectation_const d (n + 1) μ pe β
    (integrable_boltzmann μ hpe_meas hpe β) c

theorem integerLocalGibbsExpectation_add
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O P : IntegerLocalObservable d G) (n : ℕ) :
    integerLocalGibbsExpectation μ pe β
        (IntegerLocalObservable.add O P) n =
      integerLocalGibbsExpectation μ pe β O n +
        integerLocalGibbsExpectation μ pe β P n := by
  unfold integerLocalGibbsExpectation
  rw [show
    (IntegerLocalObservable.add O P).realize n =
      fun A => O.realize n A + P.realize n A by
        funext A
        exact IntegerLocalObservable.realize_add O P n A]
  exact expectation_add d (n + 1) μ pe β
    (integrable_integerRealize_gibbs μ hpe_meas hpe β O n)
    (integrable_integerRealize_gibbs μ hpe_meas hpe β P n)

theorem integerLocalGibbsExpectation_smul
    (μ : Measure G) (pe : G → ℝ) (β c : ℝ)
    (O : IntegerLocalObservable d G) (n : ℕ) :
    integerLocalGibbsExpectation μ pe β
        (IntegerLocalObservable.smul c O) n =
      c * integerLocalGibbsExpectation μ pe β O n := by
  unfold integerLocalGibbsExpectation expectation
  rw [show
    (IntegerLocalObservable.smul c O).realize n =
      fun A => c * O.realize n A by
        funext A
        exact IntegerLocalObservable.realize_smul c O n A]
  exact integral_const_mul c (O.realize n)

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem natCast_natMod (a : ℤ) (N : ℕ) (hN : 0 < N) :
    ((a.natMod N : ℕ) : ℤ) = a % (N : ℤ) := by
  have hNz : (N : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  simp [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg _ hNz)]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem natMod_add_one (a : ℤ) (N : ℕ) (hN : 0 < N) :
    (a.natMod N + 1) % N = (a + 1).natMod N := by
  apply Int.ofNat_injective
  change
    (((a.natMod N : ℕ) : ℤ) + 1) % (N : ℤ) =
      (((a + 1).natMod N : ℕ) : ℤ)
  rw [natCast_natMod a N hN, natCast_natMod (a + 1) N hN]
  exact Int.emod_add_emod a N 1

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem natMod_sub_one (a : ℤ) (N : ℕ) (hN : 0 < N) :
    (a.natMod N + N - 1) % N = (a - 1).natMod N := by
  have hplus :=
    natMod_add_one (a - 1) N hN
  have hback :
      (((a - 1).natMod N + 1) % N + N - 1) % N =
        (a - 1).natMod N := by
    have hq : (a - 1).natMod N < N :=
      Int.natMod_lt (Nat.ne_of_gt hN)
    by_cases hlast : (a - 1).natMod N + 1 = N
    · rw [hlast, Nat.mod_self, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega : N - 1 < N)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega :
          (a - 1).natMod N + 1 < N)]
      rw [show (a - 1).natMod N + 1 + N - 1 =
          (a - 1).natMod N + N by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  rw [show a - 1 + 1 = a by omega] at hplus
  rw [hplus] at hback
  exact hback

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem IntegerLocalObservable.edgeAt_vadd_unitVector
    (O : IntegerLocalObservable d G) (i : Fin d) (n : ℕ)
    (s : O.Support) :
    (IntegerLocalObservable.unitVector i +ᵥ O).edgeAt n s =
      ⟨(O.edgeAt n s).1.shift i, rfl⟩ := by
  apply Subtype.ext
  change ConcreteEdge.mk _ _ true = ConcreteEdge.mk _ _ true
  congr 1
  funext j
  apply Fin.ext
  by_cases hji : j = i
  · subst j
    simp only [IntegerLocalObservable.edgeAt,
      IntegerLocalObservable.unitVector, FinBox.shift, Pi.single_eq_same,
      if_pos, IntegerLocalObservable.coord_vadd, Pi.single_apply]
    exact (natMod_add_one ((O.coord s).1 i) (n + 1) (by omega)).symm
  · simp [IntegerLocalObservable.edgeAt, IntegerLocalObservable.unitVector,
      FinBox.shift, Pi.single_apply, hji]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem IntegerLocalObservable.edgeAt_vadd_negUnitVector
    (O : IntegerLocalObservable d G) (i : Fin d) (n : ℕ)
    (s : O.Support) :
    (IntegerLocalObservable.negUnitVector i +ᵥ O).edgeAt n s =
      ⟨(O.edgeAt n s).1.shiftBack i, rfl⟩ := by
  apply Subtype.ext
  change ConcreteEdge.mk _ _ true = ConcreteEdge.mk _ _ true
  congr 1
  funext j
  apply Fin.ext
  by_cases hji : j = i
  · subst j
    simp only [IntegerLocalObservable.edgeAt,
      IntegerLocalObservable.negUnitVector, FinBox.shiftBack,
      Pi.single_eq_same, if_pos, IntegerLocalObservable.coord_vadd,
      Pi.single_apply]
    simpa [sub_eq_add_neg] using
      (natMod_sub_one ((O.coord s).1 i) (n + 1) (by omega)).symm
  · simp [IntegerLocalObservable.edgeAt,
      IntegerLocalObservable.negUnitVector, FinBox.shiftBack,
      Pi.single_apply, hji]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem IntegerLocalObservable.realize_latticeShiftForward
    (O : IntegerLocalObservable d G) (i : Fin d) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    O.realize n (latticeShiftForward i A) =
      (IntegerLocalObservable.unitVector i +ᵥ O).realize n A := by
  apply congrArg O.kernel
  funext s
  change A ((O.edgeAt n s).1.shift i) =
    A (((IntegerLocalObservable.unitVector i +ᵥ O).edgeAt n s).1)
  exact congrArg A
    (congrArg Subtype.val
      (O.edgeAt_vadd_unitVector i n s)).symm

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem IntegerLocalObservable.realize_latticeShift
    (O : IntegerLocalObservable d G) (i : Fin d) (n : ℕ)
    (A : GaugeConfig d (n + 1) G) :
    O.realize n (latticeShift i A) =
      (IntegerLocalObservable.negUnitVector i +ᵥ O).realize n A := by
  apply congrArg O.kernel
  funext s
  change A ((O.edgeAt n s).1.shiftBack i) =
    A (((IntegerLocalObservable.negUnitVector i +ᵥ O).edgeAt n s).1)
  exact congrArg A
    (congrArg Subtype.val
      (O.edgeAt_vadd_negUnitVector i n s)).symm

theorem integerLocalGibbsExpectation_vadd_unitVector
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (i : Fin d) (n : ℕ) :
    integerLocalGibbsExpectation μ pe β
        (IntegerLocalObservable.unitVector i +ᵥ O) n =
      integerLocalGibbsExpectation μ pe β O n := by
  unfold integerLocalGibbsExpectation expectation
  have h := integral_latticeShiftForward_gibbs
    (d := d) (N := n + 1) μ pe β i (O.realize n)
  simpa only [O.realize_latticeShiftForward i n] using h

theorem integerLocalGibbsExpectation_vadd_negUnitVector
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (i : Fin d) (n : ℕ) :
    integerLocalGibbsExpectation μ pe β
        (IntegerLocalObservable.negUnitVector i +ᵥ O) n =
      integerLocalGibbsExpectation μ pe β O n := by
  unfold integerLocalGibbsExpectation expectation
  have h := integral_latticeShift_gibbs
    (d := d) (N := n + 1) μ pe β i (O.realize n)
  simpa only [O.realize_latticeShift i n] using h

/-- Exact finite-volume invariance under an arbitrary integer displacement
in one coordinate. -/
theorem integerLocalGibbsExpectation_vadd_single
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (i : Fin d) (k : ℤ) (n : ℕ) :
    integerLocalGibbsExpectation μ pe β
        ((Pi.single i k : Fin d → ℤ) +ᵥ O) n =
      integerLocalGibbsExpectation μ pe β O n := by
  cases k with
  | ofNat k =>
      induction k generalizing O with
      | zero =>
          simpa using congrArg
            (fun P : IntegerLocalObservable d G =>
              integerLocalGibbsExpectation μ pe β P n)
            (IntegerLocalObservable.zero_vadd O)
      | succ k ih =>
          have hv :
              Pi.single i (Int.ofNat (k + 1)) =
                IntegerLocalObservable.unitVector i +
                  Pi.single i (Int.ofNat k) := by
            funext j
            by_cases hji : j = i
            · subst j
              simp only [IntegerLocalObservable.unitVector,
                Pi.single_eq_same, Pi.add_apply]
              simpa [Nat.succ_eq_add_one, add_comm] using
                (Int.ofNat_add_one_out k).symm
            · simp [IntegerLocalObservable.unitVector,
                Pi.single_apply, hji]
          rw [hv, IntegerLocalObservable.add_vadd]
          exact
            (integerLocalGibbsExpectation_vadd_unitVector
              μ pe β
                ((Pi.single i (Int.ofNat k) : Fin d → ℤ) +ᵥ O)
                i n).trans
              (ih (O := O))
  | negSucc k =>
      induction k generalizing O with
      | zero =>
          simpa [IntegerLocalObservable.negUnitVector] using
            integerLocalGibbsExpectation_vadd_negUnitVector
              μ pe β O i n
      | succ k ih =>
          have hv :
              Pi.single i (Int.negSucc (k + 1)) =
                IntegerLocalObservable.negUnitVector i +
                  Pi.single i (Int.negSucc k) := by
            funext j
            by_cases hji : j = i
            · subst j
              simp only [IntegerLocalObservable.negUnitVector,
                Pi.single_eq_same, Pi.add_apply]
              omega
            · simp [IntegerLocalObservable.negUnitVector,
                Pi.single_apply, hji]
          rw [hv, IntegerLocalObservable.add_vadd]
          exact
            (integerLocalGibbsExpectation_vadd_negUnitVector
              μ pe β
                ((Pi.single i (Int.negSucc k) : Fin d → ℤ) +ᵥ O)
                i n).trans
              (ih (O := O))

/-- **Exact finite-volume invariance under the full translation group
`ℤ^d`.** -/
theorem integerLocalGibbsExpectation_vadd
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (z : Fin d → ℤ) (n : ℕ) :
    integerLocalGibbsExpectation μ pe β (z +ᵥ O) n =
      integerLocalGibbsExpectation μ pe β O n := by
  have hfin :
      ∀ S : Finset (Fin d),
        integerLocalGibbsExpectation μ pe β
            ((∑ i ∈ S, Pi.single i (z i)) +ᵥ O) n =
          integerLocalGibbsExpectation μ pe β O n := by
    intro S
    induction S using Finset.induction_on generalizing O with
    | empty =>
        simpa using congrArg
          (fun P : IntegerLocalObservable d G =>
            integerLocalGibbsExpectation μ pe β P n)
          (IntegerLocalObservable.zero_vadd O)
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi, IntegerLocalObservable.add_vadd]
        exact
          (integerLocalGibbsExpectation_vadd_single
            μ pe β ((∑ j ∈ S, Pi.single j (z j)) +ᵥ O)
              i (z i) n).trans
            (ih (O := O))
  simpa [Finset.univ_sum_single z] using
    hfin (Finset.univ : Finset (Fin d))

end IntegerExpectation

end YangMills
