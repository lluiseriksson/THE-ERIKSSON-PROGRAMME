/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Cluster

/-!
# KP2a (cont.) — the Ursell / Mayer cluster coefficient

The combinatorial coefficient at the heart of the Mayer cluster expansion of
`log Ξ` (`docs/kp-cluster-expansion-plan.md`, KP2).

For an `n`-tuple of polymers `X : Fin n → Polymer`, the **Ursell coefficient** is
the signed count of *connected spanning subgraphs* of the incompatibility graph:

  `φ(X) = ∑_{G ⊆ incompGraph X, G connected spanning} (−1)^{#edges(G)}`.

A spanning subgraph on the vertex set `Fin n` is identified with a subset `E` of
the incompatibility graph's edge finset; the subgraph is `SimpleGraph.fromEdgeSet E`
(same `n` vertices, edges `E`), and "connected spanning" is its connectedness.

`classical` supplies the decidability needed to enumerate subgraphs (the polymer
system carries no `DecidableRel` on incompatibility), so `ursell` is `noncomputable`.

This file's goal is the **definition** (the milestone is having `φ` well-typed and
oracle-clean).  Its values on small clusters and the expansion identity are the
next sub-steps; the inductive KP convergence bound (KP2b) is the months-long crux.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

variable (P : PolymerSystem)

/-- The **Ursell / Mayer coefficient** of an `n`-tuple of polymers: the signed
count `∑ (−1)^{#edges}` over connected spanning subgraphs of the incompatibility
graph (subsets `E` of its edge finset whose `fromEdgeSet` is connected). -/
noncomputable def ursell {n : ℕ} (X : Fin n → P.Polymer) : ℤ := by
  classical
  exact ∑ E ∈ (incompGraph P X).edgeFinset.powerset.filter
      (fun E : Finset (Sym2 (Fin n)) =>
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Connected),
    (-1 : ℤ) ^ E.card

/-- **Base case: a single-polymer cluster has Ursell coefficient `1`.**  Its
incompatibility graph is `⊥` on one vertex (no edges possible), whose only
connected spanning subgraph is the empty one, contributing `(−1)^0 = 1`.  This
validates the definition and is the `n = 1` base of the cluster expansion. -/
theorem ursell_fin_one (X : Fin 1 → P.Polymer) : ursell P X = 1 := by
  classical
  -- The incompatibility graph has no edges (single vertex), computed directly to
  -- avoid the dependent rewrite `incompGraph P X → ⊥` (its `Fintype` instance depends
  -- on `incompGraph P X`).
  have hef : (incompGraph P X).edgeFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet, incompGraph_adj] at he
      exact he.1 (Subsingleton.elim a b)
  have hconn : (SimpleGraph.fromEdgeSet
      (↑(∅ : Finset (Sym2 (Fin 1))) : Set (Sym2 (Fin 1)))).Connected := by
    have he : SimpleGraph.fromEdgeSet
        (↑(∅ : Finset (Sym2 (Fin 1))) : Set (Sym2 (Fin 1))) = ⊥ := by simp
    rw [he]
    refine ⟨fun u v => ?_⟩
    obtain rfl := Subsingleton.elim u v
    exact SimpleGraph.Reachable.refl _
  unfold ursell
  rw [hef, Finset.powerset_empty, Finset.filter_singleton, if_pos hconn,
      Finset.sum_singleton, Finset.card_empty]
  norm_num

/-- **Only clusters contribute.**  If the incompatibility graph of the tuple is not
connected (the tuple is not a cluster), then no spanning subgraph can be connected
either, so the Ursell coefficient vanishes.  This is the structural fact that makes
*clusters* exactly the index set of the Mayer expansion of `log Ξ`. -/
theorem ursell_eq_zero_of_not_isCluster {n : ℕ} (X : Fin n → P.Polymer)
    (h : ¬ IsCluster P X) : ursell P X = 0 := by
  classical
  unfold ursell
  have hempty : (incompGraph P X).edgeFinset.powerset.filter
      (fun E : Finset (Sym2 (Fin n)) =>
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Connected) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro E hE hconn
    rw [Finset.mem_powerset] at hE
    apply h
    have hle : SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))) ≤ incompGraph P X := by
      rw [← SimpleGraph.fromEdgeSet_edgeSet (incompGraph P X)]
      apply SimpleGraph.fromEdgeSet_mono
      rw [← SimpleGraph.coe_edgeFinset]
      exact Finset.coe_subset.mpr hE
    exact SimpleGraph.Connected.mono hle hconn
  rw [hempty, Finset.sum_empty]

/-- **First nontrivial Mayer coefficient: a "dimer" has Ursell coefficient `−1`.**
For two mutually incompatible polymers, the incompatibility graph is a single edge
on two vertices; its only connected spanning subgraph is the edge itself, giving
`(−1)^1 = −1`.  (Monomer `+1`, dimer `−1`, non-cluster `0` — matching the physical
Mayer coefficients, which validates the definition.) -/
theorem ursell_fin_two (X : Fin 2 → P.Polymer) (hinc : P.incomp (X 0) (X 1)) :
    ursell P X = -1 := by
  classical
  have hadj01 : (incompGraph P X).Adj 0 1 := by
    rw [incompGraph_adj]; exact ⟨by decide, hinc⟩
  -- The incompatibility graph has exactly the edge `s(0,1)`.
  have hef : (incompGraph P X).edgeFinset = {s(0, 1)} := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, Finset.mem_singleton]
    refine Sym2.ind (fun a b => ?_) e
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro hab
      have hne : a ≠ b := ((incompGraph_adj P X a b).mp hab).1
      fin_cases a <;> fin_cases b <;> simp_all
    · intro he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb
      · exact hadj01
      · exact (incompGraph P X).symm hadj01
  -- The empty subgraph on two vertices is disconnected; the single edge is connected.
  have hdisc : ¬ (SimpleGraph.fromEdgeSet
      (↑(∅ : Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2)))).Connected := by
    have he0 : SimpleGraph.fromEdgeSet
        (↑(∅ : Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2))) = ⊥ := by simp
    rw [he0]
    intro hc
    have : (0 : Fin 2) = 1 := SimpleGraph.reachable_bot.mp (hc.preconnected 0 1)
    exact absurd this (by decide)
  have hconn : (SimpleGraph.fromEdgeSet
      (↑({s(0, 1)} : Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2)))).Connected := by
    have hadj : (SimpleGraph.fromEdgeSet
        (↑({s(0, 1)} : Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2)))).Adj 0 1 := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by simp, by decide⟩
    refine ⟨fun u v => ?_⟩
    fin_cases u <;> fin_cases v
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _
  unfold ursell
  rw [hef]
  rw [show ({s(0, 1)} : Finset (Sym2 (Fin 2))).powerset = {∅, {s(0, 1)}} by
        ext S; rw [Finset.mem_powerset, Finset.subset_singleton_iff, Finset.mem_insert,
          Finset.mem_singleton]]
  rw [Finset.filter_insert, if_neg hdisc, Finset.filter_singleton, if_pos hconn,
      Finset.sum_singleton, Finset.card_singleton]
  norm_num

/-- **k = 2 checkpoint of `ursell(K_{k+1}) = (−1)^k·k!`: a triangle has `φ = +2`.**
Three mutually incompatible polymers have incompatibility graph `K_3` (edge set
`{s(0,1), s(0,2), s(1,2)}`).  Of the eight spanning subgraphs, the four connected
ones are the three 2-edge paths (`(−1)^2 = +1` each) and the full triangle
(`(−1)^3 = −1`), so `φ = 3·(+1) + (−1) = 2 = (−1)^2·2!`.  This is the first nontrivial
confirmation of Target A beyond the monomer (`+1`) and dimer (`−1`).

The connectivity of each concrete subgraph is settled by `decide` (kernel-reduced, so
the oracle stays `[propext, Classical.choice, Quot.sound]`); the spanning subgraphs are
enumerated as the explicit 8-element powerset of the edge set. -/
theorem ursell_fin_three (X : Fin 3 → P.Polymer)
    (h01 : P.incomp (X 0) (X 1)) (h02 : P.incomp (X 0) (X 2))
    (h12 : P.incomp (X 1) (X 2)) :
    ursell P X = 2 := by
  classical
  have h10 := P.incomp_symm _ _ h01
  have h20 := P.incomp_symm _ _ h02
  have h21 := P.incomp_symm _ _ h12
  -- The incompatibility graph is K_3: edgeFinset = {s(0,1), s(0,2), s(1,2)}.
  have hef : (incompGraph P X).edgeFinset = {s(0,1), s(0,2), s(1,2)} := by
    ext e
    rw [SimpleGraph.mem_edgeFinset]
    refine Sym2.ind (fun a b => ?_) e
    rw [SimpleGraph.mem_edgeSet, incompGraph_adj]
    fin_cases a <;> fin_cases b <;>
      simp_all [Finset.mem_insert, Finset.mem_singleton]
  -- Enumerate the 8 spanning subgraphs; resolve connectivity by `decide`.
  rw [ursell, hef, Finset.sum_filter]
  rw [show ({s(0,1), s(0,2), s(1,2)} : Finset (Sym2 (Fin 3))).powerset =
      {∅, {s(0,1)}, {s(0,2)}, {s(1,2)}, {s(0,1), s(0,2)}, {s(0,1), s(1,2)},
       {s(0,2), s(1,2)}, {s(0,1), s(0,2), s(1,2)}} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  decide

/-- **Back half of Target A: the closed form follows from the recurrence.**
The Ursell value of the complete graph, `d(k) := φ(K_{k+1})`, is conjectured to satisfy
the recurrence `d(k) = −k · d(k−1)` (the component-of-vertex-0 decomposition — the one
remaining hard combinatorial lemma).  *Granting* that recurrence, this pure induction
delivers the closed form `φ(K_{k+1}) = (−1)^k · k!` of Target A.

The hypothesis `hrec` is exactly the recurrence `c(n+1) = −n · c(n)` (for `n ≥ 1`); the
verified data `ursell_fin_one/two/three` (`d(0)=1, d(1)=−1, d(2)=2`) confirm it at the
first steps (`−1=−1·1`, `2=−2·(−1)`).  This isolates Target A's open content to the
single combinatorial recurrence, with no axiom introduced: the recurrence enters only
as an explicit hypothesis. -/
theorem closed_form_of_recurrence (c : ℕ → ℤ) (h1 : c 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n → c (n + 1) = -(n : ℤ) * c n) :
    ∀ n : ℕ, c (n + 1) = (-1) ^ n * (Nat.factorial n : ℤ) := by
  intro n
  induction n with
  | zero => simpa using h1
  | succ m ih =>
    rw [hrec (m + 1) (by omega), ih, Nat.factorial_succ]
    push_cast
    ring

/-- The **canonical complete (all-incompatible) polymer system**: every pair of
polymers is incompatible.  For any tuple `X : Fin n → ℕ`, its incompatibility graph is
the complete graph `K_n` (adjacency `i ≠ j ∧ True ↔ i ≠ j`), so this system isolates
the complete-graph Ursell values, independent of which polymers are chosen. -/
def completeSystem : PolymerSystem where
  Polymer := Unit
  incomp _ _ := True
  incomp_symm _ _ _ := trivial
  incomp_self _ := trivial
  activity _ := 1

/-- The **complete-graph Ursell value** `d(n) = φ(K_n)`, realized as the Ursell
coefficient of an `n`-tuple in the all-incompatible system.  This is the sequence
Target A computes: `d(n) = (−1)^{n-1}(n-1)!`. -/
noncomputable def ursellComplete (n : ℕ) : ℤ :=
  ursell completeSystem (fun _ : Fin n => ())

theorem ursellComplete_one : ursellComplete 1 = 1 := by
  unfold ursellComplete; exact ursell_fin_one completeSystem _

theorem ursellComplete_two : ursellComplete 2 = -1 := by
  unfold ursellComplete; exact ursell_fin_two completeSystem _ trivial

theorem ursellComplete_three : ursellComplete 3 = 2 := by
  unfold ursellComplete; exact ursell_fin_three completeSystem _ trivial trivial trivial

/-- **Target A, conditional on the recurrence.**  Granting the complete-graph Ursell
recurrence `d(n+1) = −n·d(n)` (`hrec`, the remaining open combinatorial lemma — the
component-of-vertex-0 decomposition of spanning subgraphs), the closed form
`φ(K_{n+1}) = d(n+1) = (−1)^n·n!` of Target A follows for the genuine complete-graph
values.  Validated base data: `ursellComplete_one/two/three` give `d(1)=1, d(2)=−1,
d(3)=2`, matching the recurrence (`−1 = −1·1`, `2 = −2·(−1)`).  No axiom is introduced:
the recurrence is an explicit hypothesis. -/
theorem ursellComplete_closed_form
    (hrec : ∀ n : ℕ, 1 ≤ n → ursellComplete (n + 1) = -(n : ℤ) * ursellComplete n) :
    ∀ n : ℕ, ursellComplete (n + 1) = (-1) ^ n * (Nat.factorial n : ℤ) :=
  closed_form_of_recurrence ursellComplete ursellComplete_one hrec

/-- **Recurrence ingredient `a(n) = [n ≤ 1]`: the signed sum over ALL spanning
subgraphs of `K_n` vanishes for `n ≥ 2`.**  Since `∑_{E ⊆ S} (−1)^{|E|} = (1−1)^{|S|}`
(`Finset.sum_powerset_neg_one_pow_card`), summing over every subset of the edge set of
`K_n` gives `1` when `K_n` has no edges (`n ≤ 1`) and `0` otherwise.  This `a(n)` is the
left-hand side of the cluster recurrence: expanding `a(n)` by the connected component of
vertex 0 yields `a(n) = ∑_k C(n−1,k−1)·d(k)·a(n−k)`, which with `a(n) = [n≤1]` collapses
to `d(n+1) = −n·d(n)` (the open `hrec`).  Proving that expansion is the remaining
combinatorial step (see `docs/kp-cluster-expansion-plan.md`). -/
theorem allSubgraphs_signedSum (n : ℕ) :
    ∑ E ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset, (-1 : ℤ) ^ E.card
      = if n ≤ 1 then 1 else 0 := by
  rw [Finset.sum_powerset_neg_one_pow_card]
  have hbot : (⊤ : SimpleGraph (Fin n)) = ⊥ ↔ n ≤ 1 := by
    rw [← Fin.subsingleton_iff_le_one]
    constructor
    · intro h
      refine ⟨fun a b => ?_⟩
      by_contra hab
      have hadj : (⊤ : SimpleGraph (Fin n)).Adj a b := (SimpleGraph.top_adj a b).mpr hab
      rw [h] at hadj
      exact (SimpleGraph.bot_adj a b).mp hadj
    · intro h
      ext a b
      rw [SimpleGraph.top_adj, SimpleGraph.bot_adj]
      simp [Subsingleton.elim a b]
  simp only [SimpleGraph.edgeFinset_eq_empty, hbot]

end YangMills.KP
