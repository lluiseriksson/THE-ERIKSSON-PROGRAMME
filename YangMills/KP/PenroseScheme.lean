/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Ursell
import YangMills.KP.PenrosePrep

/-!
# T2 (Penrose scheme skeleton) — partition schemes bound the Ursell coefficient

Step (i) of Target B (`docs/HANDOFF-KP.md`) is the **Penrose tree-graph
inequality** `|ursell P X| ≤ #(spanning trees of incompGraph P X)`.  Its proof
has two layers:

1. **The partition-scheme mechanism** (this file, *proved*): if a map `π`
   sends every connected spanning subgraph to a spanning tree, and each fiber
   `π⁻¹(T)` is a Boolean interval `{E : T ⊆ E ⊆ R(T)}`, then the signed sum
   telescopes — each fiber contributes `(−1)^{|T|}·[R(T) = T]` — so
   `|ursell| ≤ #trees`.  The two ingredients are:
   * `interval_signed_sum` — the Boolean-interval signed sum
     `∑_{T ⊆ E ⊆ R} (−1)^{|E|} = (−1)^{|T|}·[R = T]`;
   * `abs_signedSum_le_of_scheme` — the abstract fiberwise assembly;
   * `abs_ursell_le_card_spanningTrees` — the graph-level statement, with the
     scheme `(π, R)` as explicit hypotheses.

2. **The concrete scheme construction** (open): the breadth-first/greedy
   Penrose map `π` and its envelope `R` for an arbitrary incompatibility
   graph, with the verification that fibers are exactly intervals.  This is
   the remaining combinatorial content of step (i); it enters here only as
   the explicit hypotheses `hmaps`/`hfiber` — never as an axiom.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph

/-- Instance-agnostic form of `SimpleGraph.mem_edgeFinset`: the `Fintype`
instance is a plain implicit argument, so rewriting unifies it with whatever
instance the goal or hypothesis carries (instead of re-synthesizing one). -/
private lemma mem_edgeFinset_iff' {V : Type*} {G : SimpleGraph V}
    {inst : Fintype G.edgeSet} {e : Sym2 V} :
    e ∈ @SimpleGraph.edgeFinset V G inst ↔ e ∈ G.edgeSet :=
  SimpleGraph.mem_edgeFinset

/-- **Boolean-interval signed sum.**  For `T ⊆ R`, the signed sum over the
interval `{E : T ⊆ E ⊆ R}` collapses: `∑ (−1)^{|E|} = (−1)^{|T|}` if `R = T`
(the interval is the single point `T`) and `0` otherwise (the free part
`R \ T` contributes `(1−1)^{|R\T|}`). -/
lemma interval_signed_sum {α : Type*} [DecidableEq α] {T R : Finset α}
    (hTR : T ⊆ R) :
    ∑ E ∈ R.powerset.filter (fun E => T ⊆ E), (-1 : ℤ) ^ E.card
      = if R = T then (-1 : ℤ) ^ T.card else 0 := by
  classical
  have hbij : ∑ E ∈ R.powerset.filter (fun E => T ⊆ E), (-1 : ℤ) ^ E.card
      = ∑ A ∈ (R \ T).powerset, (-1 : ℤ) ^ (T.card + A.card) := by
    refine Finset.sum_nbij' (fun E => E \ T) (fun A => T ∪ A) ?_ ?_ ?_ ?_ ?_
    · intro E hE
      rw [Finset.mem_filter, Finset.mem_powerset] at hE
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hE.1 (Finset.Subset.refl T)
    · intro A hA
      rw [Finset.mem_powerset] at hA
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hTR (hA.trans Finset.sdiff_subset),
        Finset.subset_union_left⟩
    · intro E hE
      rw [Finset.mem_filter] at hE
      exact Finset.union_sdiff_of_subset hE.2
    · intro A hA
      rw [Finset.mem_powerset] at hA
      exact Finset.union_sdiff_cancel_left
        ((Finset.sdiff_disjoint.mono_left hA).symm)
    · intro E hE
      rw [Finset.mem_filter] at hE
      show (-1 : ℤ) ^ E.card = (-1 : ℤ) ^ (T.card + (E \ T).card)
      congr 1
      have h1 : (E \ T).card + T.card = (E ∪ T).card :=
        Finset.card_sdiff_add_card E T
      rw [Finset.union_eq_left.mpr hE.2] at h1
      omega
  rw [hbij]
  have hfactor : ∑ A ∈ (R \ T).powerset, (-1 : ℤ) ^ (T.card + A.card)
      = (-1 : ℤ) ^ T.card * ∑ A ∈ (R \ T).powerset, (-1 : ℤ) ^ A.card := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun A _ => by rw [pow_add]
  rw [hfactor, Finset.sum_powerset_neg_one_pow_card]
  by_cases h : R = T
  · rw [if_pos h, h, Finset.sdiff_self, if_pos rfl, mul_one]
  · rw [if_neg h, if_neg (fun hempty : R \ T = ∅ =>
      h (Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp hempty) hTR)), mul_zero]

/-- **Abstract partition-scheme bound.**  If `π` maps a family `S` of finsets
into a family `Tr` ("trees"), and each fiber of `π` over `T ∈ Tr` is exactly
the Boolean interval `{E : T ⊆ E ⊆ R T}`, then the signed sum over `S` is
bounded by `#Tr`: each fiber telescopes to `±1` or `0`
(`interval_signed_sum`). -/
lemma abs_signedSum_le_of_scheme {α : Type*} [DecidableEq α]
    (S Tr : Finset (Finset α)) (π R : Finset α → Finset α)
    (hmaps : ∀ E ∈ S, π E ∈ Tr)
    (hfiber : ∀ T ∈ Tr, ∀ E : Finset α,
      (E ∈ S ∧ π E = T) ↔ (T ⊆ E ∧ E ⊆ R T)) :
    |∑ E ∈ S, (-1 : ℤ) ^ E.card| ≤ (Tr.card : ℤ) := by
  classical
  calc |∑ E ∈ S, (-1 : ℤ) ^ E.card|
      = |∑ T ∈ Tr, ∑ E ∈ S.filter (fun E => π E = T), (-1 : ℤ) ^ E.card| := by
        rw [Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ ∑ T ∈ Tr, |∑ E ∈ S.filter (fun E => π E = T), (-1 : ℤ) ^ E.card| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ Tr, (1 : ℤ) := ?_
    _ = (Tr.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  refine Finset.sum_le_sum fun T hT => ?_
  have hfeq : S.filter (fun E => π E = T)
      = (R T).powerset.filter (fun E => T ⊆ E) := by
    ext E
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hES, hπ⟩
      have h := (hfiber T hT E).mp ⟨hES, hπ⟩
      exact ⟨h.2, h.1⟩
    · rintro ⟨hER, hTE⟩
      have h := (hfiber T hT E).mpr ⟨hTE, hER⟩
      exact ⟨h.1, h.2⟩
  rw [hfeq]
  by_cases hTR : T ⊆ R T
  · rw [interval_signed_sum hTR]
    rcases eq_or_ne (R T) T with h | h
    · rw [if_pos h, abs_pow, abs_neg, abs_one, one_pow]
    · rw [if_neg h, abs_zero]
      exact zero_le_one
  · have hempty : (R T).powerset.filter (fun E => T ⊆ E) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro E hE hTE
      rw [Finset.mem_powerset] at hE
      exact hTR (hTE.trans hE)
    rw [hempty, Finset.sum_empty, abs_zero]
    exact zero_le_one

/-- **Penrose tree-graph inequality, conditional on the scheme.**  Given a
partition scheme `(π, R)` for the connected spanning subgraphs of the
incompatibility graph — `π` lands in `spanningTrees`, and the fiber over each
tree `T` is exactly the Boolean interval `{E : T ⊆ E ⊆ R T}` — the Ursell
coefficient is bounded by the number of spanning trees:
`|ursell P X| ≤ #(spanningTrees (incompGraph P X))`.

The construction of the concrete (breadth-first Penrose) scheme and the
verification of `hmaps`/`hfiber` are the remaining open content of Target B
step (i); they are carried here as explicit hypotheses, never axioms. -/
theorem abs_ursell_le_card_spanningTrees_of_scheme (P : PolymerSystem)
    {n : ℕ} (X : Fin n → P.Polymer)
    [Fintype (incompGraph P X).edgeSet]
    (π R : Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)))
    (hmaps : ∀ E : Finset (Sym2 (Fin n)),
      (∀ e ∈ E, e ∈ (incompGraph P X).edgeSet) →
      (fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Connected →
      π E ∈ spanningTrees (incompGraph P X))
    (hfiber : ∀ T ∈ spanningTrees (incompGraph P X),
      ∀ E : Finset (Sym2 (Fin n)),
      ((∀ e ∈ E, e ∈ (incompGraph P X).edgeSet) ∧
        (fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Connected ∧ π E = T)
      ↔ (T ⊆ E ∧ E ⊆ R T)) :
    |ursell P X| ≤ ((spanningTrees (incompGraph P X)).card : ℤ) := by
  classical
  unfold ursell
  refine abs_signedSum_le_of_scheme _ (spanningTrees (incompGraph P X))
    π R ?_ ?_
  · intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE
    refine hmaps E (fun e he => ?_) hE.2
    have h := hE.1 he
    rwa [mem_edgeFinset_iff'] at h
  · intro T hT E
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hsub, hconn⟩, hπ⟩
      refine (hfiber T hT E).mp ⟨fun e he => ?_, hconn, hπ⟩
      have h := hsub he
      rwa [mem_edgeFinset_iff'] at h
    · intro h
      obtain ⟨hsub, hconn, hπ⟩ := (hfiber T hT E).mpr h
      refine ⟨⟨fun e he => ?_, hconn⟩, hπ⟩
      rw [mem_edgeFinset_iff']
      exact hsub e he

end YangMills.KP
