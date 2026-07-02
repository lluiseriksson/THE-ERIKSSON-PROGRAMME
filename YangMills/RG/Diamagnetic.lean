/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.MatrixRealization
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Finite-dimensional diamagnetic substrate

This file starts the source-independent, finite-dimensional bookkeeping for the
flow/diamagnetic campaign.  It deliberately stays below the heat-kernel theorem:
the concrete bridge from matrix-valued unitary transports to this linear-isometry
interface is still an open PR1 step.  The point of this module is to make the
killed-region walk convention and the finite isometry-sum estimate available
without using a Frobenius/default matrix norm shortcut.
-/

open scoped BigOperators

namespace YangMills.RG

/-- Endpoint index for an `n`-step finite walk. -/
def finalWalkIndex (n : ℕ) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

/-- A finite walk whose vertices remain in the killed region `Ω`.  The
adjacency relation is explicit so this structure cannot be inhabited by an
arbitrary endpoint-matching vertex sequence. -/
structure WalksInside (V : Type*) (Adj : V → V → Prop) (Ω : Set V) (x y : V) (n : ℕ) where
  vertex : Fin (n + 1) → V
  start_eq : vertex 0 = x
  stop_eq : vertex (finalWalkIndex n) = y
  inside : ∀ i, vertex i ∈ Ω
  step : ∀ i : Fin n, Adj (vertex i.castSucc) (vertex i.succ)

namespace WalksInside

/-- The zero-step inside walk, used as the first nonempty sanity witness. -/
def refl {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x : V} (hx : x ∈ Ω) :
    WalksInside V Adj Ω x x 0 where
  vertex := fun _ => x
  start_eq := rfl
  stop_eq := rfl
  inside := fun _ => hx
  step := fun i => Fin.elim0 i

lemma start_mem {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x y : V} {n : ℕ}
    (γ : WalksInside V Adj Ω x y n) : x ∈ Ω := by
  simpa [γ.start_eq] using γ.inside 0

lemma stop_mem {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x y : V} {n : ℕ}
    (γ : WalksInside V Adj Ω x y n) : y ∈ Ω := by
  simpa [γ.stop_eq] using γ.inside (finalWalkIndex n)

/-- Zero-step inside walks are exactly the diagonal inside witness. -/
theorem nonempty_zero_iff {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x y : V} :
    Nonempty (WalksInside V Adj Ω x y 0) ↔ x = y ∧ x ∈ Ω := by
  constructor
  · rintro ⟨γ⟩
    constructor
    · calc
        x = γ.vertex 0 := γ.start_eq.symm
        _ = y := by
          simpa [finalWalkIndex] using γ.stop_eq
    · exact γ.start_mem
  · rintro ⟨rfl, hx⟩
    exact ⟨WalksInside.refl hx⟩

lemma one_step_adj {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x y : V}
    (γ : WalksInside V Adj Ω x y 1) : Adj x y := by
  have hstop : γ.vertex (1 : Fin 2) = y := by
    simpa [finalWalkIndex] using γ.stop_eq
  simpa [hstop, γ.start_eq] using γ.step 0

/-- A one-step inside walk from one admissible adjacency edge. -/
def single {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x y : V}
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : Adj x y) : WalksInside V Adj Ω x y 1 where
  vertex := Fin.cases x (fun _ => y)
  start_eq := rfl
  stop_eq := rfl
  inside := by
    intro i
    fin_cases i <;> assumption
  step := by
    intro i
    fin_cases i
    exact hxy

/-- Prepend one admissible edge to an inside walk.  This is the recursion
constructor behind the later scalar walk-count/power bridge. -/
def cons {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x y z : V} {n : ℕ}
    (hx : x ∈ Ω) (hxy : Adj x y) (γ : WalksInside V Adj Ω y z n) :
    WalksInside V Adj Ω x z (n + 1) where
  vertex := Fin.cases x γ.vertex
  start_eq := rfl
  stop_eq := by
    simpa [finalWalkIndex] using γ.stop_eq
  inside := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hx
    · intro j
      exact γ.inside j
  step := by
    intro i
    refine Fin.cases ?_ ?_ i
    · change Adj x (γ.vertex 0)
      simpa [γ.start_eq] using hxy
    · intro j
      simpa using γ.step j

/-- Remove the first edge of a positive-length inside walk. -/
def tail {V : Type*} {Adj : V → V → Prop} {Ω : Set V} {x z : V} {n : ℕ}
    (γ : WalksInside V Adj Ω x z (n + 1)) :
    WalksInside V Adj Ω (γ.vertex 1) z n where
  vertex := fun i => γ.vertex i.succ
  start_eq := rfl
  stop_eq := by
    simpa [finalWalkIndex] using γ.stop_eq
  inside := fun i => γ.inside i.succ
  step := by
    intro i
    simpa using γ.step i.succ

end WalksInside

/-- A finite regular ambient graph interface with killed neighbors obtained by
filtering by `Ω`.  The degree is the ambient full degree; killing never changes
the scalar comparison's ambient degree convention. -/
structure FiniteAmbientRegularGraph (V : Type*) where
  neighbor : V → Finset V
  degree : ℕ
  degree_eq : ∀ x, (neighbor x).card = degree

namespace FiniteAmbientRegularGraph

variable {V : Type*} (G : FiniteAmbientRegularGraph V)

/-- Dirichlet-killed neighbor set: keep only ambient neighbors that remain in `Ω`. -/
def killedNeighbors (Ω : Set V) [DecidablePred (· ∈ Ω)] (x : V) : Finset V :=
  (G.neighbor x).filter (fun y => y ∈ Ω)

lemma mem_killedNeighbors (Ω : Set V) [DecidablePred (· ∈ Ω)] {x y : V} :
    y ∈ G.killedNeighbors Ω x ↔ y ∈ G.neighbor x ∧ y ∈ Ω := by
  exact Finset.mem_filter

/-- A killed neighbor gives a one-step inside walk for the ambient adjacency
relation, provided the starting vertex is also inside the killed region. -/
def oneStepWalkOfMemKilledNeighbors (Ω : Set V) [DecidablePred (· ∈ Ω)] {x y : V}
    (hx : x ∈ Ω) (hy : y ∈ G.killedNeighbors Ω x) :
    WalksInside V (fun a b => b ∈ G.neighbor a) Ω x y 1 :=
  WalksInside.single hx ((G.mem_killedNeighbors Ω).mp hy).2 ((G.mem_killedNeighbors Ω).mp hy).1

/-- Prepend one killed-neighbor edge to an existing inside walk. -/
def consOfMemKilledNeighbors (Ω : Set V) [DecidablePred (· ∈ Ω)] {x y z : V} {n : ℕ}
    (hx : x ∈ Ω) (hy : y ∈ G.killedNeighbors Ω x)
    (γ : WalksInside V (fun a b => b ∈ G.neighbor a) Ω y z n) :
    WalksInside V (fun a b => b ∈ G.neighbor a) Ω x z (n + 1) :=
  WalksInside.cons hx ((G.mem_killedNeighbors Ω).mp hy).1 γ

/-- Nonempty walks extend by one killed-neighbor edge at the front. -/
lemma nonempty_walk_succ_of_mem_killedNeighbors
    (Ω : Set V) [DecidablePred (· ∈ Ω)] {x y z : V} {n : ℕ}
    (hx : x ∈ Ω) (hy : y ∈ G.killedNeighbors Ω x)
    (hwalk : Nonempty (WalksInside V (fun a b => b ∈ G.neighbor a) Ω y z n)) :
    Nonempty (WalksInside V (fun a b => b ∈ G.neighbor a) Ω x z (n + 1)) := by
  rcases hwalk with ⟨γ⟩
  exact ⟨G.consOfMemKilledNeighbors Ω hx hy γ⟩

/-- Positive-length inside walks split into a first killed neighbor and a tail. -/
theorem nonempty_walk_succ_iff_exists_killedNeighbor
    (Ω : Set V) [DecidablePred (· ∈ Ω)] {x z : V} {n : ℕ} (hx : x ∈ Ω) :
    Nonempty (WalksInside V (fun a b => b ∈ G.neighbor a) Ω x z (n + 1)) ↔
      ∃ y, y ∈ G.killedNeighbors Ω x ∧
        Nonempty (WalksInside V (fun a b => b ∈ G.neighbor a) Ω y z n) := by
  constructor
  · rintro ⟨γ⟩
    refine ⟨γ.vertex 1, ?_, ⟨γ.tail⟩⟩
    rw [G.mem_killedNeighbors Ω]
    exact ⟨by simpa [γ.start_eq] using γ.step 0, γ.inside 1⟩
  · rintro ⟨y, hy, hwalk⟩
    exact G.nonempty_walk_succ_of_mem_killedNeighbors Ω hx hy hwalk

/-- A one-step ambient-neighbor walk inside `Ω` ends at a killed neighbor. -/
lemma mem_killedNeighbors_of_walk_one (Ω : Set V) [DecidablePred (· ∈ Ω)] {x y : V}
    (γ : WalksInside V (fun a b => b ∈ G.neighbor a) Ω x y 1) :
    y ∈ G.killedNeighbors Ω x := by
  rw [G.mem_killedNeighbors Ω]
  exact ⟨γ.one_step_adj, γ.stop_mem⟩

/-- With the start vertex in `Ω`, one-step inside walks are equivalent to
membership in the killed-neighbor set. -/
theorem nonempty_walk_one_iff_mem_killedNeighbors
    (Ω : Set V) [DecidablePred (· ∈ Ω)] {x y : V} (hx : x ∈ Ω) :
    Nonempty (WalksInside V (fun a b => b ∈ G.neighbor a) Ω x y 1) ↔
      y ∈ G.killedNeighbors Ω x := by
  constructor
  · rintro ⟨γ⟩
    exact G.mem_killedNeighbors_of_walk_one Ω γ
  · intro hy
    exact ⟨G.oneStepWalkOfMemKilledNeighbors Ω hx hy⟩

lemma killedNeighbors_subset (Ω : Set V) [DecidablePred (· ∈ Ω)] (x : V) :
    G.killedNeighbors Ω x ⊆ G.neighbor x := by
  intro y hy
  exact Finset.mem_of_mem_filter y hy

lemma killedNeighbors_card_le_degree (Ω : Set V) [DecidablePred (· ∈ Ω)] (x : V) :
    (G.killedNeighbors Ω x).card ≤ G.degree := by
  rw [← G.degree_eq x]
  exact Finset.card_le_card (G.killedNeighbors_subset Ω x)

/-- Endpoints reachable by `n` killed-neighbor steps, as a finite set.  This is
the scalar counting side of the later walk-power bridge. -/
def killedReachable (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ℕ → V → Finset V
  | 0, x => if x ∈ Ω then {x} else ∅
  | n + 1, x =>
      if x ∈ Ω then (G.killedNeighbors Ω x).biUnion fun y => killedReachable Ω n y else ∅

/-- The finite reachable-endpoint recursion matches nonempty inside walks. -/
theorem mem_killedReachable_iff_nonempty_walk
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ∀ {n : ℕ} {x z : V},
      z ∈ killedReachable G Ω n x ↔
        Nonempty (WalksInside V (fun a b => b ∈ G.neighbor a) Ω x z n)
  | 0, x, z => by
      by_cases hx : x ∈ Ω
      · simp [killedReachable, hx, WalksInside.nonempty_zero_iff, eq_comm]
      · simp [killedReachable, hx, WalksInside.nonempty_zero_iff]
  | n + 1, x, z => by
      by_cases hx : x ∈ Ω
      · rw [killedReachable, if_pos hx, Finset.mem_biUnion]
        constructor
        · rintro ⟨y, hy, hzy⟩
          exact nonempty_walk_succ_of_mem_killedNeighbors G Ω hx hy
            ((mem_killedReachable_iff_nonempty_walk Ω).mp hzy)
        · intro hwalk
          rw [nonempty_walk_succ_iff_exists_killedNeighbor G Ω hx] at hwalk
          rcases hwalk with ⟨y, hy, htail⟩
          exact ⟨y, hy, (mem_killedReachable_iff_nonempty_walk Ω).mpr htail⟩
      · rw [killedReachable, if_neg hx]
        simp
        exact ⟨fun γ => hx γ.start_mem⟩

/-- Any nonempty reachable-endpoint set starts from a vertex inside the killed
region. -/
theorem start_mem_of_mem_killedReachable
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] {n : ℕ} {x z : V}
    (hz : z ∈ killedReachable G Ω n x) : x ∈ Ω := by
  rcases (mem_killedReachable_iff_nonempty_walk G Ω).mp hz with ⟨γ⟩
  exact γ.start_mem

/-- Every reachable endpoint remains inside the killed region. -/
theorem stop_mem_of_mem_killedReachable
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] {n : ℕ} {x z : V}
    (hz : z ∈ killedReachable G Ω n x) : z ∈ Ω := by
  rcases (mem_killedReachable_iff_nonempty_walk G Ω).mp hz with ⟨γ⟩
  exact γ.stop_mem

/-- Scalar bound for the number of distinct endpoints reachable after `n`
killed-neighbor steps.  This is **not** the multiplicity-counted walk bound
needed for the later adjacency-power identity. -/
theorem killedReachable_card_le_degree_pow
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ∀ (n : ℕ) (x : V), (killedReachable G Ω n x).card ≤ G.degree ^ n
  | 0, x => by
      by_cases hx : x ∈ Ω
      · simp [killedReachable, hx]
      · simp [killedReachable, hx]
  | n + 1, x => by
      by_cases hx : x ∈ Ω
      · rw [killedReachable, if_pos hx]
        calc
          ((G.killedNeighbors Ω x).biUnion fun y => killedReachable G Ω n y).card
              ≤ ∑ y ∈ G.killedNeighbors Ω x, (killedReachable G Ω n y).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ y ∈ G.killedNeighbors Ω x, G.degree ^ n := by
            exact Finset.sum_le_sum fun y _hy => killedReachable_card_le_degree_pow Ω n y
          _ = (G.killedNeighbors Ω x).card * G.degree ^ n := by
            simp [Finset.sum_const]
          _ ≤ G.degree * G.degree ^ n :=
            Nat.mul_le_mul_right _ (G.killedNeighbors_card_le_degree Ω x)
          _ = G.degree ^ (n + 1) := by
            simp [pow_succ, Nat.mul_comm]
      · simp [killedReachable, hx]

/-- One-step scalar cardinality recursion for killed reachable endpoints. -/
theorem killedReachable_succ_card_le_sum
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] (n : ℕ) (x : V) :
    (killedReachable G Ω (n + 1) x).card ≤
      ∑ y ∈ G.killedNeighbors Ω x, (killedReachable G Ω n y).card := by
  by_cases hx : x ∈ Ω
  · rw [killedReachable, if_pos hx]
    exact Finset.card_biUnion_le
  · rw [killedReachable, if_neg hx]
    simp

/-- Multiplicity-counted killed walks from `x` to `z`, using the ambient
neighbor degree and the Dirichlet-killed neighbor filter.  Unlike
`killedReachable`, this is the scalar count that can feed the later
adjacency-power/walk-sum bridge. -/
def killedWalkCount (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ℕ → V → V → ℕ
  | 0, x, z => if x = z ∧ x ∈ Ω then 1 else 0
  | n + 1, x, z =>
      if x ∈ Ω then ∑ y ∈ G.killedNeighbors Ω x, killedWalkCount Ω n y z else 0

@[simp] theorem killedWalkCount_zero_self
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] {x : V} (hx : x ∈ Ω) :
    killedWalkCount G Ω 0 x x = 1 := by
  simp [killedWalkCount, hx]

theorem killedWalkCount_zero_of_ne
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] {x z : V} (hxz : x ≠ z) :
    killedWalkCount G Ω 0 x z = 0 := by
  simp [killedWalkCount, hxz]

theorem killedWalkCount_succ_eq_sum_of_mem
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] {n : ℕ} {x z : V}
    (hx : x ∈ Ω) :
    killedWalkCount G Ω (n + 1) x z =
      ∑ y ∈ G.killedNeighbors Ω x, killedWalkCount G Ω n y z := by
  simp [killedWalkCount, hx]

theorem killedWalkCount_succ_eq_zero_of_not_mem
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] {n : ℕ} {x z : V}
    (hx : x ∉ Ω) :
    killedWalkCount G Ω (n + 1) x z = 0 := by
  simp [killedWalkCount, hx]

/-- Scalar killed-neighbor transfer on endpoint-count functions.  This is the
power-iteration precursor to the later adjacency/operator bridge. -/
def killedWalkTransfer (Ω : Set V) [DecidablePred (· ∈ Ω)] (f : V → ℕ) (x : V) :
    ℕ :=
  if x ∈ Ω then ∑ y ∈ G.killedNeighbors Ω x, f y else 0

theorem killedWalkTransfer_eq_sum_of_mem
    (Ω : Set V) [DecidablePred (· ∈ Ω)] {f : V → ℕ} {x : V} (hx : x ∈ Ω) :
    killedWalkTransfer G Ω f x = ∑ y ∈ G.killedNeighbors Ω x, f y := by
  simp [killedWalkTransfer, hx]

theorem killedWalkTransfer_eq_zero_of_not_mem
    (Ω : Set V) [DecidablePred (· ∈ Ω)] {f : V → ℕ} {x : V} (hx : x ∉ Ω) :
    killedWalkTransfer G Ω f x = 0 := by
  simp [killedWalkTransfer, hx]

theorem killedWalkCount_eq_iterate_transfer
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ∀ (n : ℕ) (x z : V),
      killedWalkCount G Ω n x z =
        ((killedWalkTransfer G Ω)^[n]) (fun w => if w = z ∧ w ∈ Ω then 1 else 0) x
  | 0, x, z => by
      simp [killedWalkCount]
  | n + 1, x, z => by
      simp [Function.iterate_succ_apply', killedWalkCount, killedWalkTransfer,
        killedWalkCount_eq_iterate_transfer Ω n]

/-- Real linear killed-neighbor transfer.  This is the finite operator-power
object that mirrors the scalar killed-walk count before any matrix-valued
transport or exponential kernel is introduced. -/
def killedAdjacencyOperator (Ω : Set V) [DecidablePred (· ∈ Ω)] :
    (V → ℝ) →ₗ[ℝ] V → ℝ where
  toFun f x := if x ∈ Ω then ∑ y ∈ G.killedNeighbors Ω x, f y else 0
  map_add' f g := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hx, Finset.sum_add_distrib]
    · simp [hx]
  map_smul' c f := by
    ext x
    by_cases hx : x ∈ Ω
    · simp [hx, Finset.mul_sum]
    · simp [hx]

theorem killedAdjacencyOperator_apply
    (Ω : Set V) [DecidablePred (· ∈ Ω)] (f : V → ℝ) (x : V) :
    killedAdjacencyOperator G Ω f x =
      if x ∈ Ω then ∑ y ∈ G.killedNeighbors Ω x, f y else 0 := rfl

theorem killedAdjacencyOperator_pow_delta_eq_killedWalkCount
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ∀ (n : ℕ) (x z : V),
      ((killedAdjacencyOperator G Ω) ^ n)
          (fun w => if w = z ∧ w ∈ Ω then (1 : ℝ) else 0) x =
        (killedWalkCount G Ω n x z : ℝ)
  | 0, x, z => by
      simp [killedWalkCount]
  | n + 1, x, z => by
      by_cases hx : x ∈ Ω
      · rw [killedWalkCount_succ_eq_sum_of_mem G Ω hx]
        simp [pow_succ', killedAdjacencyOperator_apply, hx,
          killedAdjacencyOperator_pow_delta_eq_killedWalkCount Ω n]
      · rw [killedWalkCount_succ_eq_zero_of_not_mem G Ω hx]
        simp [pow_succ', killedAdjacencyOperator_apply, hx]

lemma exists_mem_of_sum_pos_nat {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (hpos : 0 < ∑ a ∈ s, f a) : ∃ a ∈ s, 0 < f a := by
  induction s using Finset.induction_on with
  | empty =>
      simp at hpos
  | insert a s ha ih =>
      rw [Finset.sum_insert ha] at hpos
      by_cases hfa : 0 < f a
      · exact ⟨a, Finset.mem_insert_self a s, hfa⟩
      · have hzero : f a = 0 := Nat.eq_zero_of_not_pos hfa
        rcases ih (by simpa [hzero] using hpos) with ⟨b, hb, hbpos⟩
        exact ⟨b, Finset.mem_insert_of_mem hb, hbpos⟩

theorem mem_killedReachable_of_killedWalkCount_pos
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ∀ (n : ℕ) (x z : V),
      0 < killedWalkCount G Ω n x z → z ∈ killedReachable G Ω n x
  | 0, x, z => by
      intro hpos
      by_cases hxz : x = z
      · subst z
        by_cases hx : x ∈ Ω
        · simp [killedReachable, hx]
        · simp [killedWalkCount, hx] at hpos
      · simp [killedWalkCount, hxz] at hpos
  | n + 1, x, z => by
      intro hpos
      by_cases hx : x ∈ Ω
      · rw [killedWalkCount_succ_eq_sum_of_mem G Ω hx] at hpos
        rcases exists_mem_of_sum_pos_nat (G.killedNeighbors Ω x)
            (fun y => killedWalkCount G Ω n y z) hpos with ⟨y, hy, hypos⟩
        rw [killedReachable, if_pos hx, Finset.mem_biUnion]
        exact ⟨y, hy, mem_killedReachable_of_killedWalkCount_pos Ω n y z hypos⟩
      · rw [killedWalkCount_succ_eq_zero_of_not_mem G Ω hx] at hpos
        exact False.elim (Nat.lt_irrefl 0 hpos)

/-- Multiplicity-counted scalar killed-walk bound.  This is the finite
ambient-degree estimate that the endpoint-reachability bound alone cannot
provide. -/
theorem killedWalkCount_le_degree_pow
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] :
    ∀ (n : ℕ) (x z : V), killedWalkCount G Ω n x z ≤ G.degree ^ n
  | 0, x, z => by
      by_cases hxz : x = z
      · subst z
        by_cases hx : x ∈ Ω
        · simp [killedWalkCount, hx]
        · simp [killedWalkCount, hx]
      · simp [killedWalkCount, hxz]
  | n + 1, x, z => by
      by_cases hx : x ∈ Ω
      · rw [killedWalkCount_succ_eq_sum_of_mem G Ω hx]
        calc
          (∑ y ∈ G.killedNeighbors Ω x, killedWalkCount G Ω n y z)
              ≤ ∑ y ∈ G.killedNeighbors Ω x, G.degree ^ n := by
            exact Finset.sum_le_sum fun y _hy => killedWalkCount_le_degree_pow Ω n y z
          _ = (G.killedNeighbors Ω x).card * G.degree ^ n := by
            simp [Finset.sum_const]
          _ ≤ G.degree * G.degree ^ n :=
            Nat.mul_le_mul_right _ (G.killedNeighbors_card_le_degree Ω x)
          _ = G.degree ^ (n + 1) := by
            simp [pow_succ, Nat.mul_comm]
      · rw [killedWalkCount_succ_eq_zero_of_not_mem G Ω hx]
        exact Nat.zero_le _

end FiniteAmbientRegularGraph

/-- Linear-isometry transport domination for a finite path family: summing one
isometric block contribution over a finite family costs only the number of
paths.  A later PR1 bridge must still convert concrete unitary block matrices
into this `LinearIsometry` interface. -/
theorem norm_sum_linearIsometry_apply_le_card
    {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (s : Finset ι) (T : ι → E →ₛₗᵢ[RingHom.id 𝕜] E) (v : E) :
    ‖∑ i ∈ s, T i v‖ ≤ (s.card : ℝ) * ‖v‖ := by
  calc
    ‖∑ i ∈ s, T i v‖ ≤ ∑ i ∈ s, ‖T i v‖ := norm_sum_le s (fun i => T i v)
    _ = ∑ i ∈ s, ‖v‖ := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact LinearIsometry.norm_map (T i) v
    _ = (s.card : ℝ) * ‖v‖ := by
      rw [Finset.sum_const, nsmul_eq_mul]

end YangMills.RG
