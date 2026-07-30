/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalObservableSubstrate

/-!
# Finite-volume invariance under translation generators

This module proves invariance under each admissible positive unit translation
generator before any thermodynamic limit is claimed.  A periodic lattice shift
permutes positive-edge coordinates, leaves the Wilson action and the genuine
Gibbs measure invariant, and is bridged to the volume-independent coordinates
of `CompatibleLocalObservable`.

The terminal theorem is `localGibbsExpectation_translate` for one generator.
Its explicit admissibility guard is essential: translating the abstract
coordinates raises `minVolume` by one, so the unguarded statement would be
false at the first admissible volume.  Iteration and a packaged action of the
full translation group are not claimed here.

This remains finite-volume substrate.  It neither constructs an
infinite-volume state nor asserts convergence of local Gibbs expectations.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

def ConcreteEdge.shift (i : Fin d) (e : ConcreteEdge d N) :
    ConcreteEdge d N :=
  { e with source := e.source.shift i }

def ConcreteEdge.shiftBack (i : Fin d) (e : ConcreteEdge d N) :
    ConcreteEdge d N :=
  { e with source := e.source.shiftBack i }

omit [NeZero d] in
@[simp]
theorem ConcreteEdge.shift_shiftBack (i : Fin d) (e : ConcreteEdge d N) :
    (e.shiftBack i).shift i = e := by
  cases e
  simp [ConcreteEdge.shift, ConcreteEdge.shiftBack, FinBox.shift_shiftBack]

omit [NeZero d] in
@[simp]
theorem ConcreteEdge.shiftBack_shift (i : Fin d) (e : ConcreteEdge d N) :
    (e.shift i).shiftBack i = e := by
  cases e
  simp [ConcreteEdge.shift, ConcreteEdge.shiftBack, FinBox.shiftBack_shift]

def posEdgeShiftEquiv (i : Fin d) : PosEdge d N ≃ PosEdge d N where
  toFun e := ⟨e.1.shift i, e.2⟩
  invFun e := ⟨e.1.shiftBack i, e.2⟩
  left_inv e := by
    apply Subtype.ext
    exact ConcreteEdge.shiftBack_shift i e.1
  right_inv e := by
    apply Subtype.ext
    exact ConcreteEdge.shift_shiftBack i e.1

/-- Pull a gauge field back by one positive lattice shift. -/
def latticeShift (i : Fin d) (A : GaugeConfig d N G) :
    GaugeConfig d N G where
  toFun e := A (e.shiftBack i)
  map_reverse e := by
    simpa [ConcreteEdge.shiftBack, finBoxGeometry_reverse] using
      A.map_reverse (e.shiftBack i)

def ConcretePlaquette.shift (i : Fin d) (p : ConcretePlaquette d N) :
    ConcretePlaquette d N :=
  { p with site := p.site.shift i }

def ConcretePlaquette.shiftBack (i : Fin d) (p : ConcretePlaquette d N) :
    ConcretePlaquette d N :=
  { p with site := p.site.shiftBack i }

omit [NeZero d] in
@[simp]
theorem ConcretePlaquette.shift_shiftBack (i : Fin d)
    (p : ConcretePlaquette d N) :
    (p.shiftBack i).shift i = p := by
  cases p
  simp [ConcretePlaquette.shift, ConcretePlaquette.shiftBack,
    FinBox.shift_shiftBack]

omit [NeZero d] in
@[simp]
theorem ConcretePlaquette.shiftBack_shift (i : Fin d)
    (p : ConcretePlaquette d N) :
    (p.shift i).shiftBack i = p := by
  cases p
  simp [ConcretePlaquette.shift, ConcretePlaquette.shiftBack,
    FinBox.shiftBack_shift]

def plaquetteShiftEquiv (i : Fin d) :
    ConcretePlaquette d N ≃ ConcretePlaquette d N where
  toFun p := p.shift i
  invFun p := p.shiftBack i
  left_inv := ConcretePlaquette.shiftBack_shift i
  right_inv := ConcretePlaquette.shift_shiftBack i

omit [NeZero d] in
theorem ConcretePlaquette.shiftBack_edges (i : Fin d)
    (p : ConcretePlaquette d N) (k : Fin 4) :
    (p.shiftBack i).edges k = (p.edges k).shiftBack i := by
  fin_cases k <;>
    simp [ConcretePlaquette.shiftBack, ConcretePlaquette.edges,
      ConcreteEdge.shiftBack, FinBox.shift_shiftBack_comm]

omit [MeasurableSpace G] in
theorem plaquetteHolonomy_latticeShift (i : Fin d)
    (A : GaugeConfig d N G) (p : ConcretePlaquette d N) :
    GaugeConfig.plaquetteHolonomy (latticeShift i A) p =
      GaugeConfig.plaquetteHolonomy A (p.shiftBack i) := by
  unfold GaugeConfig.plaquetteHolonomy latticeShift
  change
    A ((p.edges 0).shiftBack i) * A ((p.edges 1).shiftBack i) *
        A ((p.edges 2).shiftBack i) * A ((p.edges 3).shiftBack i) =
      A ((p.shiftBack i).edges 0) * A ((p.shiftBack i).edges 1) *
        A ((p.shiftBack i).edges 2) * A ((p.shiftBack i).edges 3)
  rw [ConcretePlaquette.shiftBack_edges i p 0,
    ConcretePlaquette.shiftBack_edges i p 1,
    ConcretePlaquette.shiftBack_edges i p 2,
    ConcretePlaquette.shiftBack_edges i p 3]

omit [MeasurableSpace G] in
theorem wilsonAction_latticeShift (pe : G → ℝ) (i : Fin d)
    (A : GaugeConfig d N G) :
    wilsonAction pe (latticeShift i A) = wilsonAction pe A := by
  unfold wilsonAction
  simp_rw [plaquetteHolonomy_latticeShift]
  exact (plaquetteShiftEquiv (d := d) (N := N) i).symm.sum_comp
    (fun p => pe (GaugeConfig.plaquetteHolonomy A p))

theorem integral_latticeShift
    (μ : Measure G) [IsProbabilityMeasure μ] (i : Fin d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : GaugeConfig d N G → E) :
    ∫ A, f (latticeShift i A) ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∫ A, f A ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  have hmeas : gaugeMeasureFrom (d := d) (N := N) μ
      = Measure.map (gaugeConfigMEquiv (d := d) (N := N) (G := G))
          (Measure.pi (fun _ : PosEdge d N => μ)) := rfl
  rw [hmeas, integral_map_equiv, integral_map_equiv]
  let e := posEdgeShiftEquiv (d := d) (N := N) i
  let T := MeasurableEquiv.piCongrLeft (fun _ : PosEdge d N => G) e
  have hact : ∀ x : PosEdge d N → G,
      latticeShift i (gaugeConfigMEquiv x) = gaugeConfigMEquiv (T x) := by
    intro x
    apply (gaugeConfigEquiv (d := d) (N := N) (G := G)).symm.injective
    funext a
    change configToPos (latticeShift i (gaugeConfigMEquiv x)) a =
      configToPos (gaugeConfigMEquiv (T x)) a
    change (gaugeConfigMEquiv x) (a.1.shiftBack i) =
      configToPos (gaugeConfigMEquiv (T x)) a
    rw [show (gaugeConfigMEquiv x) (a.1.shiftBack i) =
      configToPos (gaugeConfigMEquiv x) ⟨a.1.shiftBack i, a.2⟩ from rfl]
    rw [show configToPos (gaugeConfigMEquiv x) = x from
      (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv x]
    rw [show configToPos (gaugeConfigMEquiv (T x)) = T x from
      (gaugeConfigEquiv (d := d) (N := N) (G := G)).left_inv (T x)]
    symm
    have hT : T x (e (e.symm a)) = x (e.symm a) :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : PosEdge d N => G) e x (e.symm a)
    rw [e.apply_symm_apply] at hT
    calc
      T x a = x (e.symm a) := hT
      _ = x ⟨a.1.shiftBack i, a.2⟩ := by rfl
  simp_rw [hact]
  have hmp : MeasurePreserving T
      (Measure.pi (fun _ : PosEdge d N => μ))
      (Measure.pi (fun _ : PosEdge d N => μ)) := by
    exact measurePreserving_piCongrLeft (fun _ : PosEdge d N => μ)
      (posEdgeShiftEquiv (d := d) (N := N) i)
  exact hmp.integral_comp T.measurableEmbedding
    (fun y => f (gaugeConfigMEquiv y))

theorem integral_latticeShift_gibbs
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ) (i : Fin d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : GaugeConfig d N G → E) :
    ∫ A, f (latticeShift i A)
        ∂(gibbsMeasure (d := d) (N := N) μ pe β)
      = ∫ A, f A ∂(gibbsMeasure (d := d) (N := N) μ pe β) := by
  unfold gibbsMeasure
  rw [integral_tilted, integral_tilted]
  have hgoal := integral_latticeShift (d := d) (N := N) μ i
    (fun B => (Real.exp (-β * wilsonAction pe B) /
      ∫ x, Real.exp (-β * wilsonAction pe x)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) • f B)
  simp only [wilsonAction_latticeShift pe i] at hgoal
  exact hgoal

/-! ### Translation of compatible local observables -/

/-- The inverse action to `latticeShift`: pull a gauge field forward by one
positive lattice shift.  This is the variance that pairs with adding `eᵢ` to
the abstract coordinates of a local observable. -/
def latticeShiftForward (i : Fin d) (A : GaugeConfig d N G) :
    GaugeConfig d N G where
  toFun e := A (e.shift i)
  map_reverse e := by
    simpa [ConcreteEdge.shift, finBoxGeometry_reverse] using
      A.map_reverse (e.shift i)

omit [MeasurableSpace G] in
@[simp]
theorem latticeShift_latticeShiftForward (i : Fin d)
    (A : GaugeConfig d N G) :
    latticeShift i (latticeShiftForward i A) = A := by
  apply GaugeConfig.ext'
  intro e
  simp [latticeShift, latticeShiftForward]

omit [MeasurableSpace G] in
@[simp]
theorem latticeShiftForward_latticeShift (i : Fin d)
    (A : GaugeConfig d N G) :
    latticeShiftForward i (latticeShift i A) = A := by
  apply GaugeConfig.ext'
  intro e
  simp [latticeShift, latticeShiftForward]

/-- Invariance of the product gauge measure under the forward shift, obtained
from invariance under its explicit inverse. -/
theorem integral_latticeShiftForward
    (μ : Measure G) [IsProbabilityMeasure μ] (i : Fin d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : GaugeConfig d N G → E) :
    ∫ A, f (latticeShiftForward i A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)
      = ∫ A, f A ∂(gaugeMeasureFrom (d := d) (N := N) μ) := by
  have h := integral_latticeShift (d := d) (N := N) μ i
    (fun A => f (latticeShiftForward i A))
  simpa using h.symm

/-- Invariance of the genuine finite-volume Gibbs measure under the forward
shift. -/
theorem integral_latticeShiftForward_gibbs
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ) (i : Fin d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : GaugeConfig d N G → E) :
    ∫ A, f (latticeShiftForward i A)
        ∂(gibbsMeasure (d := d) (N := N) μ pe β)
      = ∫ A, f A ∂(gibbsMeasure (d := d) (N := N) μ pe β) := by
  have h := integral_latticeShift_gibbs (d := d) (N := N) μ pe β i
    (fun A => f (latticeShiftForward i A))
  simpa using h.symm

namespace CompatibleLocalObservable

/-- Translate the volume-independent support coordinates by one positive unit
in direction `i`.  The larger `minVolume` is essential: without it, the
translated realization can take the undersized-volume zero branch while the
original does not. -/
noncomputable def translate
    (O : CompatibleLocalObservable d G) (i : Fin d) :
    CompatibleLocalObservable d G where
  Support := O.Support
  coord := fun s =>
    ⟨fun j => (O.coord s).1 j + if j = i then 1 else 0, (O.coord s).2⟩
  coord_injective := by
    intro s t hst
    apply O.coord_injective
    apply Prod.ext
    · funext j
      have hj := congrArg (fun c => c.1 j) hst
      simp only at hj
      omega
    · have hdir := congrArg Prod.snd hst
      simpa using hdir
  minVolume := O.minVolume + 1
  coord_lt := by
    intro s j
    have hj := O.coord_lt s j
    dsimp
    split_ifs <;> omega
  kernel := O.kernel
  kernel_measurable := O.kernel_measurable
  bound := O.bound
  bound_nonneg := O.bound_nonneg
  kernel_bound := O.kernel_bound

omit [NeZero d] [Group G] [MeasurableSpace G] in
/-- Reduction modulo the torus side commutes with a positive unit
translation. -/
theorem mod_add_one_mod {a m : ℕ} (hm : 1 < m) :
    (a % m + 1) % m = (a + 1) % m := by
  calc
    (a % m + 1) % m = (a % m + 1 % m) % m := by
      rw [Nat.mod_eq_of_lt hm]
    _ = (a + 1) % m := (Nat.add_mod a 1 m).symm

omit [NeZero d] [Group G] in
/-- The edge obtained by realizing the translated abstract coordinate is the
positive shift of the edge realizing the original coordinate. -/
theorem edgeAt_translate
    (O : CompatibleLocalObservable d G) (i : Fin d) (n : ℕ)
    (hO : O.minVolume ≤ n)
    (hT : (O.translate i).minVolume ≤ n) (s : O.Support) :
    (O.translate i).edgeAt n hT s =
      ⟨(O.edgeAt n hO s).1.shift i, rfl⟩ := by
  have hn : 1 < n + 1 := by
    have := hT
    simp only [translate] at this
    omega
  apply Subtype.ext
  change ConcreteEdge.mk _ _ true = ConcreteEdge.mk _ _ true
  congr 1
  · funext j
    apply Fin.ext
    by_cases hji : j = i
    · subst j
      simp [edgeAt, translate, FinBox.shift,
        mod_add_one_mod hn]
    · simp [edgeAt, translate, FinBox.shift, hji]

/-- Bridge between the geometric action on configurations and translation of
the abstract local observable.  The admissibility guard is part of the
statement because the unguarded equality is false at the first volume. -/
theorem realize_latticeShiftForward
    (O : CompatibleLocalObservable d G) (i : Fin d) (n : ℕ)
    (hT : (O.translate i).minVolume ≤ n)
    (A : GaugeConfig d (n + 1) G) :
    O.realize n (latticeShiftForward i A) =
      (O.translate i).realize n A := by
  have hO : O.minVolume ≤ n := by
    have := hT
    simp only [translate] at this
    omega
  rw [realize, dif_pos hO, realize, dif_pos hT]
  apply congrArg O.kernel
  funext s
  change A ((O.edgeAt n hO s).1.shift i) =
    A (((O.translate i).edgeAt n hT s).1)
  exact congrArg A
    (congrArg Subtype.val (edgeAt_translate O i n hO hT s)).symm

end CompatibleLocalObservable

/-- Genuine finite-volume Gibbs expectations are invariant under one positive
unit translation generator of an admissible compatible local observable. -/
theorem localGibbsExpectation_translate
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (i : Fin d) (n : ℕ)
    (hT : (O.translate i).minVolume ≤ n) :
    localGibbsExpectation μ pe β (O.translate i) n =
      localGibbsExpectation μ pe β O n := by
  unfold localGibbsExpectation expectation
  have h := integral_latticeShiftForward_gibbs
    (d := d) (N := n + 1) μ pe β i (O.realize n)
  simpa only [O.realize_latticeShiftForward i n hT] using h

namespace CompatibleLocalObservable

/-- Iterate positive translation generators in the order specified by a
finite list.  This is the finite-volume centering device used by the
thermodynamic-limit comparison: a fixed list can move a local support away
from every periodic seam before a bounded cluster window is inspected. -/
noncomputable def translateList
    (O : CompatibleLocalObservable d G) :
    List (Fin d) → CompatibleLocalObservable d G
  | [] => O
  | i :: is => (O.translate i).translateList is

@[simp]
theorem translateList_nil (O : CompatibleLocalObservable d G) :
    O.translateList [] = O := rfl

@[simp]
theorem translateList_cons
    (O : CompatibleLocalObservable d G) (i : Fin d) (is : List (Fin d)) :
    O.translateList (i :: is) = (O.translate i).translateList is := rfl

@[simp]
theorem minVolume_translateList
    (O : CompatibleLocalObservable d G) (is : List (Fin d)) :
    (O.translateList is).minVolume = O.minVolume + is.length := by
  induction is generalizing O with
  | nil => simp
  | cons i is ih =>
      rw [translateList_cons, ih]
      simp only [translate, List.length_cons]
      omega

end CompatibleLocalObservable

/-- Genuine finite-volume expectations are invariant under every finite word
in the positive translation generators, once the translated observable is
admissible at that volume.  This is an iteration theorem, not yet the action
of the full infinite translation group. -/
theorem localGibbsExpectation_translateList
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (is : List (Fin d)) (n : ℕ)
    (hT : (O.translateList is).minVolume ≤ n) :
    localGibbsExpectation μ pe β (O.translateList is) n =
      localGibbsExpectation μ pe β O n := by
  induction is generalizing O with
  | nil => rfl
  | cons i is ih =>
      have htail :
          ((O.translate i).translateList is).minVolume ≤ n := by
        simpa only [CompatibleLocalObservable.translateList_cons] using hT
      calc
        localGibbsExpectation μ pe β
            ((O.translate i).translateList is) n
            = localGibbsExpectation μ pe β (O.translate i) n :=
          ih (O := O.translate i) htail
        _ = localGibbsExpectation μ pe β O n := by
          apply localGibbsExpectation_translate
          rw [CompatibleLocalObservable.minVolume_translateList] at htail
          omega

end YangMills
