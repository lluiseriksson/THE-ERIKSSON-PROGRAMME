/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.MatrixRealization
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Finite-dimensional diamagnetic substrate

This file starts the source-independent, finite-dimensional bookkeeping for the
flow/diamagnetic campaign.  It deliberately stays below the heat-kernel theorem:
unitary matrix transports are only converted into the linear-isometry interface,
and the finite killed-region walk convention plus finite isometry-sum estimate
remain available without using a Frobenius/default matrix norm shortcut.
-/

open scoped BigOperators

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A concrete complex unitary matrix acts as a linear isometry on
`EuclideanSpace ℂ n`, i.e. on the PiLp-2 model rather than the plain Pi
sup-norm model. -/
noncomputable def toEuclideanLinearIsometry (U : Matrix.unitaryGroup n ℂ) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
  LinearMap.isometryOfInner (Matrix.toEuclideanLin (U : Matrix n n ℂ)) (by
    rw [(WithLp.toLp_surjective 2).forall₂]
    intro x y
    simp only [Matrix.toLpLin_toLp, Matrix.toLin'_apply, EuclideanSpace.inner_eq_star_dotProduct]
    rw [Matrix.star_mulVec]
    rw [dotProduct_comm]
    rw [Matrix.dotProduct_mulVec]
    rw [Matrix.vecMul_vecMul]
    rw [← Matrix.star_eq_conjTranspose]
    rw [Matrix.UnitaryGroup.star_mul_self]
    simp
    rw [dotProduct_comm])

end Matrix.UnitaryGroup

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
      0 < killedWalkCount G Ω n x z → z ∈ killedReachable G Ω n x := by
  intro n
  induction n with
  | zero =>
      intro x z hpos
      by_cases hxz : x = z
      · subst z
        by_cases hx : x ∈ Ω
        · simp [killedReachable, hx]
        · simp [killedWalkCount, hx] at hpos
      · simp [killedWalkCount, hxz] at hpos
  | succ n ih =>
      intro x z hpos
      by_cases hx : x ∈ Ω
      · rw [killedWalkCount_succ_eq_sum_of_mem G Ω hx] at hpos
        rcases exists_mem_of_sum_pos_nat (G.killedNeighbors Ω x)
            (fun y => killedWalkCount G Ω n y z) hpos with ⟨y, hy, hypos⟩
        rw [killedReachable, if_pos hx, Finset.mem_biUnion]
        exact ⟨y, hy, ih y z hypos⟩
      · rw [killedWalkCount_succ_eq_zero_of_not_mem G Ω hx] at hpos
        exact False.elim (Nat.lt_irrefl 0 hpos)

/-- Positivity of the finite killed-adjacency operator-power coefficient gives
the scalar support relation.  This is still only the real scalar
operator-power bridge, not the later matrix-valued walk-sum theorem. -/
theorem mem_killedReachable_of_killedAdjacencyOperator_pow_delta_pos
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V] {n : ℕ} {x z : V}
    (hpos :
      0 <
        ((killedAdjacencyOperator G Ω) ^ n)
          (fun w => if w = z ∧ w ∈ Ω then (1 : ℝ) else 0) x) :
    z ∈ killedReachable G Ω n x := by
  rw [killedAdjacencyOperator_pow_delta_eq_killedWalkCount G Ω n x z] at hpos
  exact mem_killedReachable_of_killedWalkCount_pos G Ω n x z (by exact_mod_cast hpos)

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

/-- Block-transport coefficient recursion along killed-neighbor paths.  The
edge transports are already `LinearIsometry`s, so this substrate stays at the
operator interface and does not introduce matrix norms or exponentials. -/
def blockTransportPowerCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E) :
    ℕ → V → V → E → E
  | 0, x, z, v => if x = z ∧ x ∈ Ω then v else 0
  | n + 1, x, z, v =>
      if x ∈ Ω then
        (G.killedNeighbors Ω x).attach.sum fun y =>
          blockTransportPowerCoeff Ω T n y.1 z (T x y.1 y.2 v)
      else 0

theorem blockTransportPowerCoeff_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (x z : V) (v : E) :
    blockTransportPowerCoeff G Ω T 0 x z v =
      if x = z ∧ x ∈ Ω then v else 0 := rfl

theorem blockTransportPowerCoeff_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (n : ℕ) (x z : V) (v : E) :
    blockTransportPowerCoeff G Ω T (n + 1) x z v =
      if x ∈ Ω then
        (G.killedNeighbors Ω x).attach.sum fun y =>
          blockTransportPowerCoeff G Ω T n y.1 z (T x y.1 y.2 v)
      else 0 := rfl

/-- Bundled linear-map version of `blockTransportPowerCoeff` in the block
variable.  This is still a coefficient-level substrate: it does not package a
global ambient operator or an exponential. -/
def blockTransportPowerCoeffLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E) :
    ℕ → V → V → E →ₗ[ℝ] E
  | 0, x, z => if x = z ∧ x ∈ Ω then LinearMap.id else 0
  | n + 1, x, z =>
      if x ∈ Ω then
        (G.killedNeighbors Ω x).attach.sum fun y =>
          (blockTransportPowerCoeffLinearMap Ω T n y.1 z).comp
            (T x y.1 y.2).toLinearMap
      else 0

theorem blockTransportPowerCoeffLinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E) :
    ∀ (n : ℕ) (x z : V) (v : E),
      blockTransportPowerCoeffLinearMap G Ω T n x z v =
        blockTransportPowerCoeff G Ω T n x z v
  | 0, x, z, v => by
      by_cases hxz : x = z
      · subst z
        by_cases hx : x ∈ Ω
        · simp [blockTransportPowerCoeffLinearMap, blockTransportPowerCoeff_zero, hx]
        · simp [blockTransportPowerCoeffLinearMap, blockTransportPowerCoeff_zero, hx]
      · simp [blockTransportPowerCoeffLinearMap, blockTransportPowerCoeff_zero, hxz]
  | n + 1, x, z, v => by
      by_cases hx : x ∈ Ω
      · simp [blockTransportPowerCoeffLinearMap, blockTransportPowerCoeff_succ, hx,
          blockTransportPowerCoeffLinearMap_apply Ω T n]
      · simp [blockTransportPowerCoeffLinearMap, blockTransportPowerCoeff_succ, hx]

/-- One-step global block-transport operator on vertex-indexed blocks.

This is the linear, finite-neighbor-sum operator whose powers should later be
connected to `blockTransportPowerCoeff`.  It is not yet bundled as a continuous
operator and carries no exponential or heat-kernel claim. -/
def blockTransportStepLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E) :
    (V → E) →ₗ[ℝ] (V → E) where
  toFun f x :=
    if hx : x ∈ Ω then
      (G.killedNeighbors Ω x).attach.sum fun y => T x y.1 y.2 (f y.1)
    else 0
  map_add' f g := by
    funext x
    by_cases hx : x ∈ Ω
    · simp only [hx, ↓reduceDIte, Pi.add_apply]
      calc
        (G.killedNeighbors Ω x).attach.sum
            (fun y => T x y.1 y.2 (f y.1 + g y.1))
            =
          (G.killedNeighbors Ω x).attach.sum
            (fun y => T x y.1 y.2 (f y.1) + T x y.1 y.2 (g y.1)) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            rw [map_add]
        _ =
          (G.killedNeighbors Ω x).attach.sum (fun y => T x y.1 y.2 (f y.1)) +
            (G.killedNeighbors Ω x).attach.sum (fun y => T x y.1 y.2 (g y.1)) := by
            rw [Finset.sum_add_distrib]
    · simp [hx]
  map_smul' c f := by
    funext x
    by_cases hx : x ∈ Ω
    · simp only [hx, ↓reduceDIte, Pi.smul_apply]
      calc
        (G.killedNeighbors Ω x).attach.sum
            (fun y => T x y.1 y.2 (c • f y.1))
            =
          (G.killedNeighbors Ω x).attach.sum
            (fun y => c • T x y.1 y.2 (f y.1)) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            rw [map_smul]
        _ = c • (G.killedNeighbors Ω x).attach.sum
            (fun y => T x y.1 y.2 (f y.1)) := by
            rw [Finset.smul_sum]
    · simp [hx]

theorem blockTransportStepLinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (f : V → E) (x : V) :
    blockTransportStepLinearMap G Ω T f x =
      if hx : x ∈ Ω then
        (G.killedNeighbors Ω x).attach.sum fun y => T x y.1 y.2 (f y.1)
      else 0 := rfl

/-- One-step orientation check: applying the global block-transport step to a
delta block at `z` agrees with the recursive one-step coefficient from `x` to
`z`.  This is still a finite coefficient identity, not a heat-kernel theorem. -/
theorem blockTransportStepLinearMap_delta_eq_blockTransportPowerCoeff_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (x z : V) (v : E) :
    blockTransportStepLinearMap G Ω T (fun y => if y = z then v else 0) x =
      blockTransportPowerCoeff G Ω T 1 x z v := by
  by_cases hx : x ∈ Ω
  · rw [blockTransportStepLinearMap_apply, blockTransportPowerCoeff_succ]
    simp [hx]
    exact Finset.sum_congr
      (s₁ := (G.killedNeighbors Ω x).attach)
      (s₂ := (G.killedNeighbors Ω x).attach)
      (f := fun y => T x y.1 y.2 (if y.1 = z then v else 0))
      (g := fun y => blockTransportPowerCoeff G Ω T 0 y.1 z (T x y.1 y.2 v))
      rfl (fun y _hy => by
        by_cases hyz : y.1 = z
        · subst z
          have hz : y.1 ∈ Ω := ((G.mem_killedNeighbors Ω).mp y.2).2
          simp [blockTransportPowerCoeff_zero, hz]
        · simp [blockTransportPowerCoeff_zero, hyz])
  · rw [blockTransportStepLinearMap_apply, blockTransportPowerCoeff_succ]
    simp [hx]

/-- Left killed-region compression for the finite block-transport coefficient. -/
theorem blockTransportPowerCoeff_eq_zero_of_not_mem_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    {x : V} (hx : x ∉ Ω) :
    ∀ (n : ℕ) (z : V) (v : E),
      blockTransportPowerCoeff G Ω T n x z v = 0
  | 0, z, v => by
      simp [blockTransportPowerCoeff_zero, hx]
  | n + 1, z, v => by
      rw [blockTransportPowerCoeff_succ, if_neg hx]

/-- Right killed-region compression for the finite block-transport coefficient. -/
theorem blockTransportPowerCoeff_eq_zero_of_not_mem_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    {z : V} (hz : z ∉ Ω) :
    ∀ (n : ℕ) (x : V) (v : E),
      blockTransportPowerCoeff G Ω T n x z v = 0
  | 0, x, v => by
      by_cases hxz : x = z
      · subst z
        simp [blockTransportPowerCoeff_zero, hz]
      · simp [blockTransportPowerCoeff_zero, hxz]
  | n + 1, x, v => by
      by_cases hx : x ∈ Ω
      · rw [blockTransportPowerCoeff_succ, if_pos hx]
        exact Finset.sum_eq_zero fun y _hy =>
          blockTransportPowerCoeff_eq_zero_of_not_mem_right Ω T hz n y.1 (T x y.1 y.2 v)
      · rw [blockTransportPowerCoeff_succ, if_neg hx]

theorem norm_blockTransportPowerCoeff_succ_le_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    {n : ℕ} {x z : V} (v : E) (hx : x ∈ Ω) :
    ‖blockTransportPowerCoeff G Ω T (n + 1) x z v‖ ≤
      (G.killedNeighbors Ω x).attach.sum fun y =>
        ‖blockTransportPowerCoeff G Ω T n y.1 z (T x y.1 y.2 v)‖ := by
  rw [blockTransportPowerCoeff_succ, if_pos hx]
  exact norm_sum_le _ _

/-- Norm domination for the recursive block-transport coefficient by the
multiplicity-counted killed-walk scalar.  This is the finite power coefficient
estimate, below any semigroup-kernel statement. -/
theorem norm_blockTransportPower_delta_le_killedWalkCount
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E) :
    ∀ (n : ℕ) (x z : V) (v : E),
      ‖blockTransportPowerCoeff G Ω T n x z v‖ ≤
        (killedWalkCount G Ω n x z : ℝ) * ‖v‖ := by
  intro n
  induction n with
  | zero =>
      intro x z v
      by_cases hxz : x = z
      · subst z
        by_cases hx : x ∈ Ω
        · simp [blockTransportPowerCoeff_zero, killedWalkCount, hx]
        · simp [blockTransportPowerCoeff_zero, killedWalkCount, hx]
      · simp [blockTransportPowerCoeff_zero, killedWalkCount, hxz]
  | succ n ih =>
      intro x z v
      by_cases hx : x ∈ Ω
      · calc
          ‖blockTransportPowerCoeff G Ω T (n + 1) x z v‖
              ≤ (G.killedNeighbors Ω x).attach.sum fun y =>
                  ‖blockTransportPowerCoeff G Ω T n y.1 z (T x y.1 y.2 v)‖ :=
            norm_blockTransportPowerCoeff_succ_le_sum G Ω T v hx
          _ ≤ (G.killedNeighbors Ω x).attach.sum fun y =>
                  (killedWalkCount G Ω n y.1 z : ℝ) * ‖T x y.1 y.2 v‖ := by
            exact Finset.sum_le_sum fun y _hy => ih y.1 z (T x y.1 y.2 v)
          _ = (G.killedNeighbors Ω x).attach.sum fun y =>
                  (killedWalkCount G Ω n y.1 z : ℝ) * ‖v‖ := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            rw [LinearIsometry.norm_map]
          _ = ∑ y ∈ G.killedNeighbors Ω x, (killedWalkCount G Ω n y z : ℝ) * ‖v‖ := by
            simpa using
              (Finset.sum_attach (G.killedNeighbors Ω x)
                (fun y => (killedWalkCount G Ω n y z : ℝ) * ‖v‖))
          _ = (∑ y ∈ G.killedNeighbors Ω x, (killedWalkCount G Ω n y z : ℝ)) * ‖v‖ := by
            rw [Finset.sum_mul]
          _ = (killedWalkCount G Ω (n + 1) x z : ℝ) * ‖v‖ := by
            rw [killedWalkCount_succ_eq_sum_of_mem G Ω hx]
            simp only [Nat.cast_sum]
      · rw [blockTransportPowerCoeff_succ, if_neg hx]
        simp [killedWalkCount_succ_eq_zero_of_not_mem G Ω hx]

/-- Ambient-degree corollary for the finite block-transport power coefficient.
This packages the scalar killed-walk counting bound; it is still below any
semigroup comparison statement. -/
theorem norm_blockTransportPower_delta_le_degree_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (n : ℕ) (x z : V) (v : E) :
    ‖blockTransportPowerCoeff G Ω T n x z v‖ ≤
      (G.degree ^ n : ℝ) * ‖v‖ := by
  calc
    ‖blockTransportPowerCoeff G Ω T n x z v‖
        ≤ (killedWalkCount G Ω n x z : ℝ) * ‖v‖ :=
      norm_blockTransportPower_delta_le_killedWalkCount G Ω T n x z v
    _ ≤ (G.degree ^ n : ℝ) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast killedWalkCount_le_degree_pow G Ω n x z) (norm_nonneg v)

/-- Finite scalar coefficient bound for block-transport powers.  This is the
finite-sum substrate for later killed-kernel comparisons and keeps the
inside-domain compression in `blockTransportPowerCoeff`. -/
theorem norm_sum_smul_blockTransportPowerCoeff_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (s : Finset ℕ) (a : ℕ → ℝ) (x z : V) (v : E) :
    ‖∑ n ∈ s, a n • blockTransportPowerCoeff G Ω T n x z v‖ ≤
      (∑ n ∈ s, |a n| * (G.degree ^ n : ℝ)) * ‖v‖ := by
  calc
    ‖∑ n ∈ s, a n • blockTransportPowerCoeff G Ω T n x z v‖
        ≤ ∑ n ∈ s, ‖a n • blockTransportPowerCoeff G Ω T n x z v‖ :=
      norm_sum_le s fun n => a n • blockTransportPowerCoeff G Ω T n x z v
    _ ≤ ∑ n ∈ s, |a n| * ((G.degree ^ n : ℝ) * ‖v‖) := by
      refine Finset.sum_le_sum ?_
      intro n _hn
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (norm_blockTransportPower_delta_le_degree_pow G Ω T n x z v) (abs_nonneg (a n))
    _ = (∑ n ∈ s, |a n| * (G.degree ^ n : ℝ)) * ‖v‖ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro n _hn
      ring

/-- Finite factorial-coefficient truncation bound for block-transport powers.
This specializes the finite coefficient substrate while avoiding any infinite
series or named kernel theorem. -/
theorem norm_truncatedFactorial_blockTransportPowerCoeff_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x z : V) (v : E) :
    ‖∑ n ∈ Finset.range (N + 1),
        (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v‖ ≤
      (∑ n ∈ Finset.range (N + 1),
        (|τ| ^ n / (Nat.factorial n : ℝ)) * (G.degree ^ n : ℝ)) * ‖v‖ := by
  calc
    ‖∑ n ∈ Finset.range (N + 1),
        (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v‖
        ≤ (∑ n ∈ Finset.range (N + 1),
            |τ ^ n / (Nat.factorial n : ℝ)| * (G.degree ^ n : ℝ)) * ‖v‖ :=
      norm_sum_smul_blockTransportPowerCoeff_le G Ω T (Finset.range (N + 1))
        (fun n => τ ^ n / (Nat.factorial n : ℝ)) x z v
    _ = (∑ n ∈ Finset.range (N + 1),
          (|τ| ^ n / (Nat.factorial n : ℝ)) * (G.degree ^ n : ℝ)) * ‖v‖ := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro n _hn
      have hfac_nonneg : 0 ≤ (Nat.factorial n : ℝ) := by
        exact_mod_cast Nat.zero_le (Nat.factorial n)
      rw [abs_div, abs_pow, abs_of_nonneg hfac_nonneg]

/-- Finite factorial-coefficient truncations are bounded by the scalar
exponential majorant. This remains a finite coefficient estimate, not a
semigroup or heat-kernel theorem. -/
theorem norm_truncatedFactorial_blockTransportPowerCoeff_le_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x z : V) (v : E) :
    ‖∑ n ∈ Finset.range (N + 1),
        (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v‖ ≤
      Real.exp (|τ| * (G.degree : ℝ)) * ‖v‖ := by
  have hnonneg : 0 ≤ |τ| * (G.degree : ℝ) := by
    positivity
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
        (|τ| ^ n / (Nat.factorial n : ℝ)) * (G.degree ^ n : ℝ)) ≤
        Real.exp (|τ| * (G.degree : ℝ)) := by
    calc
      (∑ n ∈ Finset.range (N + 1),
        (|τ| ^ n / (Nat.factorial n : ℝ)) * (G.degree ^ n : ℝ))
          = ∑ n ∈ Finset.range (N + 1),
              (|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro n _hn
            rw [mul_pow]
            ring
      _ ≤ Real.exp (|τ| * (G.degree : ℝ)) :=
        Real.sum_le_exp_of_nonneg hnonneg (N + 1)
  calc
    ‖∑ n ∈ Finset.range (N + 1),
        (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v‖
        ≤ (∑ n ∈ Finset.range (N + 1),
            (|τ| ^ n / (Nat.factorial n : ℝ)) * (G.degree ^ n : ℝ)) * ‖v‖ :=
      norm_truncatedFactorial_blockTransportPowerCoeff_le G Ω T N τ x z v
    _ ≤ Real.exp (|τ| * (G.degree : ℝ)) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right hsum (norm_nonneg v)

/-- Finite factorial-coefficient block-transport object over the killed
neighbor recursion.  This only packages the already finite coefficient sum; it
is not a semigroup, heat-kernel, or infinite-series object. -/
noncomputable def truncatedFactorialBlockTransportCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x z : V) (v : E) : E :=
  ∑ n ∈ Finset.range (N + 1),
    (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v

/-- The packaged finite factorial block-transport object inherits the scalar
exponential majorant.  This is still a finite truncation estimate. -/
theorem norm_truncatedFactorialBlockTransportCoeff_le_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x z : V) (v : E) :
    ‖truncatedFactorialBlockTransportCoeff G Ω T N τ x z v‖ ≤
      Real.exp (|τ| * (G.degree : ℝ)) * ‖v‖ := by
  simpa [truncatedFactorialBlockTransportCoeff] using
    norm_truncatedFactorial_blockTransportPowerCoeff_le_exp G Ω T N τ x z v

/-- Left killed-region compression for the packaged finite factorial
block-transport object. -/
theorem truncatedFactorialBlockTransportCoeff_eq_zero_of_not_mem_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) {x : V} (hx : x ∉ Ω) (z : V) (v : E) :
    truncatedFactorialBlockTransportCoeff G Ω T N τ x z v = 0 := by
  rw [truncatedFactorialBlockTransportCoeff]
  exact Finset.sum_eq_zero fun n _hn => by
    rw [blockTransportPowerCoeff_eq_zero_of_not_mem_left G Ω T hx n z v, smul_zero]

/-- Right killed-region compression for the packaged finite factorial
block-transport object. -/
theorem truncatedFactorialBlockTransportCoeff_eq_zero_of_not_mem_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x : V) {z : V} (hz : z ∉ Ω) (v : E) :
    truncatedFactorialBlockTransportCoeff G Ω T N τ x z v = 0 := by
  rw [truncatedFactorialBlockTransportCoeff]
  exact Finset.sum_eq_zero fun n _hn => by
    rw [blockTransportPowerCoeff_eq_zero_of_not_mem_right G Ω T hz n x v, smul_zero]

/-- Explicit double-compressed finite factorial block-transport coefficient.
This is a finite truncated object with killed-region compression on both
endpoints, not an infinite semigroup or named kernel theorem. -/
noncomputable def doubleCompressedTruncatedFactorialBlockTransportCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x z : V) (v : E) : E :=
  if x ∈ Ω then
    if z ∈ Ω then truncatedFactorialBlockTransportCoeff G Ω T N τ x z v else 0
  else 0

/-- The already packaged finite coefficient is exactly its double-compressed
killed-region version.  The point is only the finite compression statement. -/
theorem truncatedFactorialBlockTransportCoeff_eq_doubleCompressed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x z : V) (v : E) :
    truncatedFactorialBlockTransportCoeff G Ω T N τ x z v =
      doubleCompressedTruncatedFactorialBlockTransportCoeff G Ω T N τ x z v := by
  by_cases hx : x ∈ Ω
  · by_cases hz : z ∈ Ω
    · simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx, hz]
    · simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx, hz,
        truncatedFactorialBlockTransportCoeff_eq_zero_of_not_mem_right G Ω T N τ x hz v]
  · simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx,
      truncatedFactorialBlockTransportCoeff_eq_zero_of_not_mem_left G Ω T N τ hx z v]

/-- The explicit double-compressed finite object inherits the scalar exponential
majorant.  This remains a finite truncation bound. -/
theorem norm_doubleCompressedTruncatedFactorialBlockTransportCoeff_le_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x z : V) (v : E) :
    ‖doubleCompressedTruncatedFactorialBlockTransportCoeff G Ω T N τ x z v‖ ≤
      Real.exp (|τ| * (G.degree : ℝ)) * ‖v‖ := by
  rw [← truncatedFactorialBlockTransportCoeff_eq_doubleCompressed G Ω T N τ x z v]
  exact norm_truncatedFactorialBlockTransportCoeff_le_exp G Ω T N τ x z v

/-- Inside both killed-region endpoints, the double-compressed finite object is
the packaged finite coefficient. -/
theorem doubleCompressedTruncatedFactorialBlockTransportCoeff_eq_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) {x z : V} (hx : x ∈ Ω) (hz : z ∈ Ω) (v : E) :
    doubleCompressedTruncatedFactorialBlockTransportCoeff G Ω T N τ x z v =
      truncatedFactorialBlockTransportCoeff G Ω T N τ x z v := by
  simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx, hz]

/-- Left outside the killed region, the explicit double-compressed finite object
vanishes by construction. -/
theorem doubleCompressedTruncatedFactorialBlockTransportCoeff_eq_zero_of_not_mem_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) {x : V} (hx : x ∉ Ω) (z : V) (v : E) :
    doubleCompressedTruncatedFactorialBlockTransportCoeff G Ω T N τ x z v = 0 := by
  simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx]

/-- Right outside the killed region, the explicit double-compressed finite object
vanishes by construction. -/
theorem doubleCompressedTruncatedFactorialBlockTransportCoeff_eq_zero_of_not_mem_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) (x : V) {z : V} (hz : z ∉ Ω) (v : E) :
    doubleCompressedTruncatedFactorialBlockTransportCoeff G Ω T N τ x z v = 0 := by
  by_cases hx : x ∈ Ω
  · simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx, hz]
  · simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx]

/-- Exact double-compressed factorial-series block-transport coefficient.
This is the totalized infinite series object with the same killed-region
compression convention as the finite truncations.  Convergence and comparison
to an operator exponential are intentionally separate obligations. -/
noncomputable def doubleCompressedFactorialBlockTransportCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) (x z : V) (v : E) : E :=
  if x ∈ Ω then
    if z ∈ Ω then
      ∑' n : ℕ,
        (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v
    else 0
  else 0

/-- Inside both killed-region endpoints, the infinite factorial-series object is
the totalized series of block-transport coefficients. -/
theorem doubleCompressedFactorialBlockTransportCoeff_eq_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) {x z : V} (hx : x ∈ Ω) (hz : z ∈ Ω) (v : E) :
    doubleCompressedFactorialBlockTransportCoeff G Ω T τ x z v =
      ∑' n : ℕ,
        (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v := by
  simp [doubleCompressedFactorialBlockTransportCoeff, hx, hz]

/-- Left outside the killed region, the infinite factorial-series object
vanishes by construction. -/
theorem doubleCompressedFactorialBlockTransportCoeff_eq_zero_of_not_mem_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) {x : V} (hx : x ∉ Ω) (z : V) (v : E) :
    doubleCompressedFactorialBlockTransportCoeff G Ω T τ x z v = 0 := by
  simp [doubleCompressedFactorialBlockTransportCoeff, hx]

/-- Right outside the killed region, the infinite factorial-series object
vanishes by construction. -/
theorem doubleCompressedFactorialBlockTransportCoeff_eq_zero_of_not_mem_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) (x : V) {z : V} (hz : z ∉ Ω) (v : E) :
    doubleCompressedFactorialBlockTransportCoeff G Ω T τ x z v = 0 := by
  by_cases hx : x ∈ Ω
  · simp [doubleCompressedFactorialBlockTransportCoeff, hx, hz]
  · simp [doubleCompressedFactorialBlockTransportCoeff, hx]

/-- Absolute convergence of the factorial block-transport coefficient series.
This is still a coefficient-series convergence statement, not an operator
exponential identity. -/
theorem summable_factorial_blockTransportPowerCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) (x z : V) (v : E) :
    Summable fun n : ℕ =>
      (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v := by
  refine Summable.of_norm ?_
  have hbase :
      Summable fun n : ℕ =>
        ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) := by
    exact Real.summable_pow_div_factorial (|τ| * (G.degree : ℝ))
  have hmajor :
      Summable fun n : ℕ =>
        ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) * ‖v‖ :=
    hbase.mul_right ‖v‖
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmajor
  intro n
  rw [norm_smul]
  calc
    |τ ^ n / (Nat.factorial n : ℝ)| * ‖blockTransportPowerCoeff G Ω T n x z v‖
        ≤ |τ ^ n / (Nat.factorial n : ℝ)| * ((G.degree ^ n : ℝ) * ‖v‖) := by
          exact mul_le_mul_of_nonneg_left
            (norm_blockTransportPower_delta_le_degree_pow G Ω T n x z v)
            (abs_nonneg _)
    _ = ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) * ‖v‖ := by
          have hfac_nonneg : 0 ≤ (Nat.factorial n : ℝ) := by
            exact_mod_cast Nat.zero_le (Nat.factorial n)
          rw [abs_div, abs_pow, abs_of_nonneg hfac_nonneg, mul_pow]
          ring

/-- The exact double-compressed factorial-series coefficient object inherits the
scalar exponential majorant.  This is still a coefficient-series bound, not an
operator exponential or semigroup identity. -/
theorem norm_doubleCompressedFactorialBlockTransportCoeff_le_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) (x z : V) (v : E) :
    ‖doubleCompressedFactorialBlockTransportCoeff G Ω T τ x z v‖ ≤
      Real.exp (|τ| * (G.degree : ℝ)) * ‖v‖ := by
  by_cases hx : x ∈ Ω
  · by_cases hz : z ∈ Ω
    · rw [doubleCompressedFactorialBlockTransportCoeff_eq_of_mem G Ω T τ hx hz v]
      let term : ℕ → E := fun n =>
        (τ ^ n / (Nat.factorial n : ℝ)) • blockTransportPowerCoeff G Ω T n x z v
      let major : ℕ → ℝ := fun n =>
        ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) * ‖v‖
      have hbase :
          Summable fun n : ℕ =>
            ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) := by
        exact Real.summable_pow_div_factorial (|τ| * (G.degree : ℝ))
      have hmajor : Summable major := hbase.mul_right ‖v‖
      have hnorms : Summable fun n : ℕ => ‖term n‖ := by
        refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmajor
        intro n
        dsimp [term, major]
        rw [norm_smul]
        calc
          |τ ^ n / (Nat.factorial n : ℝ)| * ‖blockTransportPowerCoeff G Ω T n x z v‖
              ≤ |τ ^ n / (Nat.factorial n : ℝ)| * ((G.degree ^ n : ℝ) * ‖v‖) := by
                exact mul_le_mul_of_nonneg_left
                  (norm_blockTransportPower_delta_le_degree_pow G Ω T n x z v)
                  (abs_nonneg _)
          _ = ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) * ‖v‖ := by
                have hfac_nonneg : 0 ≤ (Nat.factorial n : ℝ) := by
                  exact_mod_cast Nat.zero_le (Nat.factorial n)
                rw [abs_div, abs_pow, abs_of_nonneg hfac_nonneg, mul_pow]
                ring
      have hpoint : ∀ n : ℕ, ‖term n‖ ≤ major n := by
        intro n
        dsimp [term, major]
        rw [norm_smul]
        calc
          |τ ^ n / (Nat.factorial n : ℝ)| * ‖blockTransportPowerCoeff G Ω T n x z v‖
              ≤ |τ ^ n / (Nat.factorial n : ℝ)| * ((G.degree ^ n : ℝ) * ‖v‖) := by
                exact mul_le_mul_of_nonneg_left
                  (norm_blockTransportPower_delta_le_degree_pow G Ω T n x z v)
                  (abs_nonneg _)
          _ = ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) * ‖v‖ := by
                have hfac_nonneg : 0 ≤ (Nat.factorial n : ℝ) := by
                  exact_mod_cast Nat.zero_le (Nat.factorial n)
                rw [abs_div, abs_pow, abs_of_nonneg hfac_nonneg, mul_pow]
                ring
      have hscalar_tsum :
          (∑' n : ℕ, ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ))) ≤
            Real.exp (|τ| * (G.degree : ℝ)) := by
        refine Real.tsum_le_of_sum_range_le ?_ ?_
        · intro n
          positivity
        · intro N
          exact Real.sum_le_exp_of_nonneg (by positivity) N
      calc
        ‖∑' n : ℕ, term n‖ ≤ ∑' n : ℕ, ‖term n‖ :=
          norm_tsum_le_tsum_norm hnorms
        _ ≤ ∑' n : ℕ, major n :=
          hnorms.tsum_le_tsum hpoint hmajor
        _ = (∑' n : ℕ, ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ))) * ‖v‖ := by
          change
            (∑' n : ℕ,
              ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ)) * ‖v‖) =
              (∑' n : ℕ,
                ((|τ| * (G.degree : ℝ)) ^ n / (Nat.factorial n : ℝ))) * ‖v‖
          rw [tsum_mul_right]
        _ ≤ Real.exp (|τ| * (G.degree : ℝ)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hscalar_tsum (norm_nonneg v)
    · rw [doubleCompressedFactorialBlockTransportCoeff_eq_zero_of_not_mem_right G Ω T τ x hz v]
      simpa using mul_nonneg (Real.exp_pos (|τ| * (G.degree : ℝ))).le (norm_nonneg v)
  · rw [doubleCompressedFactorialBlockTransportCoeff_eq_zero_of_not_mem_left G Ω T τ hx z v]
    simpa using mul_nonneg (Real.exp_pos (|τ| * (G.degree : ℝ))).le (norm_nonneg v)

/-- Inside both killed-region endpoints, the finite double-compressed factorial
truncation is the corresponding finite partial sum. -/
theorem doubleCompressedTruncatedFactorialBlockTransportCoeff_eq_sum_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (N : ℕ) (τ : ℝ) {x z : V} (hx : x ∈ Ω) (hz : z ∈ Ω) (v : E) :
    doubleCompressedTruncatedFactorialBlockTransportCoeff G Ω T N τ x z v =
      ∑ k ∈ Finset.range (N + 1),
        (τ ^ k / (Nat.factorial k : ℝ)) • blockTransportPowerCoeff G Ω T k x z v := by
  rw [doubleCompressedTruncatedFactorialBlockTransportCoeff_eq_of_mem G Ω T N τ hx hz v]
  rfl

/-- Shifted finite partial sums of the factorial block-transport coefficient
series converge to the totalized coefficient series. -/
theorem tendsto_factorial_blockTransportPowerCoeff_partial_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) (x z : V) (v : E) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ k ∈ Finset.range (N + 1),
          (τ ^ k / (Nat.factorial k : ℝ)) • blockTransportPowerCoeff G Ω T k x z v)
      Filter.atTop
      (nhds
        (∑' k : ℕ,
          (τ ^ k / (Nat.factorial k : ℝ)) • blockTransportPowerCoeff G Ω T k x z v)) := by
  change
    Filter.Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          (τ ^ k / (Nat.factorial k : ℝ)) • blockTransportPowerCoeff G Ω T k x z v)
      Filter.atTop
      (nhds
        (∑' k : ℕ,
          (τ ^ k / (Nat.factorial k : ℝ)) • blockTransportPowerCoeff G Ω T k x z v))
  rw [Filter.tendsto_add_atTop_iff_nat
    (f := fun N : ℕ =>
      ∑ k ∈ Finset.range N,
        (τ ^ k / (Nat.factorial k : ℝ)) • blockTransportPowerCoeff G Ω T k x z v)
    1]
  exact (summable_factorial_blockTransportPowerCoeff G Ω T τ x z v).hasSum.tendsto_sum_nat

/-- Finite double-compressed factorial truncations converge to the exact
double-compressed factorial-series coefficient.

This is only the coefficient-series partial-sum convergence statement.  It is
not an operator exponential, semigroup identity, or heat-kernel theorem. -/
theorem tendsto_doubleCompressedTruncatedFactorialBlockTransportCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Ω : Set V) [DecidablePred (· ∈ Ω)] [DecidableEq V]
    (T : (x y : V) → y ∈ G.killedNeighbors Ω x → E →ₛₗᵢ[RingHom.id ℝ] E)
    (τ : ℝ) (x z : V) (v : E) :
    Filter.Tendsto
      (fun N : ℕ =>
        doubleCompressedTruncatedFactorialBlockTransportCoeff G Ω T N τ x z v)
      Filter.atTop
      (nhds (doubleCompressedFactorialBlockTransportCoeff G Ω T τ x z v)) := by
  by_cases hx : x ∈ Ω
  · by_cases hz : z ∈ Ω
    · rw [doubleCompressedFactorialBlockTransportCoeff_eq_of_mem G Ω T τ hx hz v]
      exact
        (tendsto_factorial_blockTransportPowerCoeff_partial_sum G Ω T τ x z v).congr
          (fun N : ℕ =>
            (doubleCompressedTruncatedFactorialBlockTransportCoeff_eq_sum_of_mem
              G Ω T N τ hx hz v).symm)
    · rw [doubleCompressedFactorialBlockTransportCoeff_eq_zero_of_not_mem_right G Ω T τ x hz v]
      simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx, hz]
  · rw [doubleCompressedFactorialBlockTransportCoeff_eq_zero_of_not_mem_left G Ω T τ hx z v]
    simp [doubleCompressedTruncatedFactorialBlockTransportCoeff, hx]

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

/-- Concrete unitary block matrices on `EuclideanSpace ℂ n` instantiate the
finite path-family linear-isometry estimate. -/
theorem norm_sum_unitary_toEuclideanLinearIsometry_apply_le_card
    {n ι : Type*} [Fintype n] [DecidableEq n]
    (s : Finset ι) (U : ι → Matrix.unitaryGroup n ℂ) (v : EuclideanSpace ℂ n) :
    ‖∑ i ∈ s, Matrix.UnitaryGroup.toEuclideanLinearIsometry (U i) v‖ ≤
      (s.card : ℝ) * ‖v‖ :=
  norm_sum_linearIsometry_apply_le_card s
    (fun i => Matrix.UnitaryGroup.toEuclideanLinearIsometry (U i)) v

end YangMills.RG
