/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Ursell
import YangMills.KP.SinglePolymer

/-!
# T1 — the complete-graph Ursell recurrence `d(n+1) = −n·d(n)`

This file closes Target A's missing combinatorial lemma (`docs/HANDOFF-KP.md`):
the complete-graph Ursell value
`d(n) = φ(K_n) = ∑_{E ⊆ E(K_n), fromEdgeSet E connected} (−1)^{|E|}`
satisfies the recurrence `d(n+1) = −n·d(n)` for `n ≥ 1`.

## Blueprint (component-of-vertex-0 decomposition)

Fiber the *all-subgraphs* signed sum
`a(n+1) = ∑_{E ⊆ E(K_{n+1})} (−1)^{|E|}` (which is `0` for `n+1 ≥ 2`, by the
verified `allSubgraphs_signedSum`) by the vertex set `S = reachSet E` of
vertices reachable from `0` in the spanning subgraph `fromEdgeSet E`:

* fibers over `S` with `0 ∉ S` are empty (`0` is always reachable from itself);
* fibers with `|Sᶜ| ≥ 2` vanish under the sign-reversing involution that
  toggles one fixed edge inside `Sᶜ` (toggling an edge between two vertices
  unreachable from `0` does not change `reachSet` — `reachable_insert_iff`);
* the fiber over `S = univ` consists exactly of the connected spanning
  subgraphs, summing to `d(n+1)`;
* each fiber with `|Sᶜ| = 1` (`S = univ \ {v}`, `v ≠ 0`; there are `n` such)
  is in sign-preserving bijection with the connected spanning subgraphs of
  `K_S ≅ K_n` via the relabeling `Fin.succAbove v`, contributing `d(n)`.

Summing: `0 = d(n+1) + n·d(n)`, the recurrence.

Combined with the verified back-half `ursellComplete_closed_form`, this makes
the closed form `φ(K_{n+1}) = (−1)^n·n!` (Target A) unconditional, and with it
the single-polymer Mayer identity `Ξ = exp(clusterSum)`
(`YangMills/KP/SinglePolymer.lean`).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open SimpleGraph

/-! ### The set of vertices reachable from `0` -/

/-- The set of vertices reachable from `0` in the spanning subgraph
`fromEdgeSet E` — the connected component of the basepoint, as a `Finset`. -/
noncomputable def reachSet (m : ℕ) (E : Finset (Sym2 (Fin (m + 1)))) :
    Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter
    (fun x => (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Reachable 0 x)

lemma mem_reachSet {m : ℕ} {E : Finset (Sym2 (Fin (m + 1)))} {x : Fin (m + 1)} :
    x ∈ reachSet m E ↔
      (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Reachable 0 x := by
  unfold reachSet
  simp

lemma zero_mem_reachSet (m : ℕ) (E : Finset (Sym2 (Fin (m + 1)))) :
    (0 : Fin (m + 1)) ∈ reachSet m E :=
  mem_reachSet.mpr (SimpleGraph.Reachable.refl 0)

lemma reachSet_mono {m : ℕ} {E F : Finset (Sym2 (Fin (m + 1)))} (h : E ⊆ F) :
    reachSet m E ⊆ reachSet m F := by
  intro x hx
  rw [mem_reachSet] at hx ⊢
  exact SimpleGraph.Reachable.mono
    (SimpleGraph.fromEdgeSet_mono (Finset.coe_subset.mpr h)) hx

/-- `fromEdgeSet E` is connected iff every vertex is reachable from `0`. -/
lemma reachSet_eq_univ_iff {m : ℕ} {E : Finset (Sym2 (Fin (m + 1)))} :
    reachSet m E = Finset.univ ↔
      (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Connected := by
  constructor
  · intro h
    rw [SimpleGraph.connected_iff]
    refine ⟨fun a b => ?_, ⟨0⟩⟩
    have ha : a ∈ reachSet m E := h ▸ Finset.mem_univ a
    have hb : b ∈ reachSet m E := h ▸ Finset.mem_univ b
    exact (mem_reachSet.mp ha).symm.trans (mem_reachSet.mp hb)
  · intro h
    ext x
    simp only [Finset.mem_univ, iff_true]
    exact mem_reachSet.mpr (h.preconnected 0 x)

/-! ### Toggling an edge between unreachable vertices -/

/-- **Toggle stability.**  Adding an edge between two vertices that are both
unreachable from `0` does not change reachability from `0`.  (A walk from `0`
can never enter the new edge: the first time it would use it, its current
vertex would already be a reachable endpoint of that edge.) -/
lemma reachable_insert_iff {m : ℕ} (E : Finset (Sym2 (Fin (m + 1))))
    {w₁ w₂ : Fin (m + 1)}
    (h1 : ¬ (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Reachable 0 w₁)
    (h2 : ¬ (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Reachable 0 w₂)
    (x : Fin (m + 1)) :
    (fromEdgeSet (↑(insert s(w₁, w₂) E) : Set (Sym2 (Fin (m + 1))))).Reachable 0 x ↔
      (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Reachable 0 x := by
  constructor
  · intro h
    obtain ⟨p⟩ := h
    have key : ∀ u y : Fin (m + 1),
        (fromEdgeSet (↑(insert s(w₁, w₂) E) : Set (Sym2 (Fin (m + 1))))).Walk u y →
        (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Reachable 0 u →
        (fromEdgeSet (↑E : Set (Sym2 (Fin (m + 1))))).Reachable 0 y := by
      intro u y p
      induction p with
      | nil => exact id
      | @cons a b c hadj ptail ih =>
        intro h0a
        apply ih
        rw [SimpleGraph.fromEdgeSet_adj] at hadj
        obtain ⟨hmem, hne⟩ := hadj
        rw [Finset.coe_insert, Set.mem_insert_iff] at hmem
        rcases hmem with he | he
        · rw [Sym2.eq_iff] at he
          rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd h0a h1
          · exact absurd h0a h2
        · exact h0a.trans (SimpleGraph.Adj.reachable
            ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨he, hne⟩))
    exact key 0 x p (SimpleGraph.Reachable.refl 0)
  · intro h
    refine SimpleGraph.Reachable.mono (SimpleGraph.fromEdgeSet_mono ?_) h
    rw [Finset.coe_insert]
    exact Set.subset_insert _ _

/-- Toggle stability, `reachSet` form. -/
lemma reachSet_insert_eq {m : ℕ} (E : Finset (Sym2 (Fin (m + 1))))
    {w₁ w₂ : Fin (m + 1)}
    (h1 : w₁ ∉ reachSet m E) (h2 : w₂ ∉ reachSet m E) :
    reachSet m (insert s(w₁, w₂) E) = reachSet m E := by
  ext x
  rw [mem_reachSet, mem_reachSet]
  exact reachable_insert_iff E (fun h => h1 (mem_reachSet.mpr h))
    (fun h => h2 (mem_reachSet.mpr h)) x

/-! ### Vanishing fibers -/

/-- Fibers over a set not containing `0` are empty. -/
lemma fiber_zero_of_zero_notMem (m : ℕ) (S : Finset (Fin (m + 1)))
    (h0 : (0 : Fin (m + 1)) ∉ S) :
    ∑ E ∈ (⊤ : SimpleGraph (Fin (m + 1))).edgeFinset.powerset.filter
        (fun E => reachSet m E = S), (-1 : ℤ) ^ E.card = 0 := by
  have hempty : (⊤ : SimpleGraph (Fin (m + 1))).edgeFinset.powerset.filter
      (fun E => reachSet m E = S) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro E _ hE
    exact h0 (hE ▸ zero_mem_reachSet m E)
  rw [hempty, Finset.sum_empty]

/-- **Involution step.**  If at least two vertices lie outside `S`, the fiber
over `S` vanishes: toggling one fixed edge inside `Sᶜ` is a sign-reversing
involution of the fiber. -/
lemma fiber_zero_of_small (m : ℕ) (S : Finset (Fin (m + 1)))
    (hcard : S.card + 2 ≤ m + 1) :
    ∑ E ∈ (⊤ : SimpleGraph (Fin (m + 1))).edgeFinset.powerset.filter
        (fun E => reachSet m E = S), (-1 : ℤ) ^ E.card = 0 := by
  classical
  -- pick two distinct vertices outside S
  have hlt : 1 < (Finset.univ \ S).card := by
    have h1 : (Finset.univ \ S).card = (m + 1) - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin]
    omega
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hlt
  have hw₁S : w₁ ∉ S := (Finset.mem_sdiff.mp hw₁).2
  have hw₂S : w₂ ∉ S := (Finset.mem_sdiff.mp hw₂).2
  have he₀top : s(w₁, w₂) ∈ (⊤ : SimpleGraph (Fin (m + 1))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
    exact hne
  refine Finset.sum_involution
    (fun E _ => if s(w₁, w₂) ∈ E then E.erase s(w₁, w₂) else insert s(w₁, w₂) E)
    ?_ ?_ ?_ ?_
  · -- the signs cancel
    intro E hE
    by_cases hmem : s(w₁, w₂) ∈ E
    · simp only [if_pos hmem]
      have hc : (E.erase s(w₁, w₂)).card + 1 = E.card :=
        Finset.card_erase_add_one hmem
      rw [← hc, pow_succ]
      ring
    · simp only [if_neg hmem]
      rw [Finset.card_insert_of_notMem hmem, pow_succ]
      ring
  · -- the involution has no fixed points
    intro E hE hf
    by_cases hmem : s(w₁, w₂) ∈ E
    · simp only [if_pos hmem]
      intro heq
      rw [← heq] at hmem
      exact Finset.notMem_erase _ _ hmem
    · simp only [if_neg hmem]
      intro heq
      apply hmem
      rw [← heq]
      exact Finset.mem_insert_self _ _
  · -- the involution preserves the fiber
    intro E hE
    rw [Finset.mem_filter, Finset.mem_powerset] at hE
    obtain ⟨hpow, hreach⟩ := hE
    by_cases hmem : s(w₁, w₂) ∈ E
    · simp only [if_pos hmem]
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨(Finset.erase_subset _ _).trans hpow, ?_⟩
      have hsub : reachSet m (E.erase s(w₁, w₂)) ⊆ reachSet m E :=
        reachSet_mono (Finset.erase_subset _ _)
      have h1 : w₁ ∉ reachSet m (E.erase s(w₁, w₂)) :=
        fun h => hw₁S (hreach ▸ hsub h)
      have h2 : w₂ ∉ reachSet m (E.erase s(w₁, w₂)) :=
        fun h => hw₂S (hreach ▸ hsub h)
      have hkey := reachSet_insert_eq (E.erase s(w₁, w₂)) h1 h2
      rw [Finset.insert_erase hmem] at hkey
      rw [← hkey]
      exact hreach
    · simp only [if_neg hmem]
      rw [Finset.mem_filter, Finset.mem_powerset]
      have h1 : w₁ ∉ reachSet m E := fun h => hw₁S (hreach ▸ h)
      have h2 : w₂ ∉ reachSet m E := fun h => hw₂S (hreach ▸ h)
      refine ⟨Finset.insert_subset he₀top hpow, ?_⟩
      rw [reachSet_insert_eq E h1 h2]
      exact hreach
  · -- the toggle is an involution
    intro E hE
    by_cases hmem : s(w₁, w₂) ∈ E
    · simp only [if_pos hmem, if_neg (Finset.notMem_erase s(w₁, w₂) E),
        Finset.insert_erase hmem]
    · simp only [if_neg hmem, if_pos (Finset.mem_insert_self s(w₁, w₂) E),
        Finset.erase_insert hmem]

/-! ### The full fiber: `S = univ` is the connected sum -/

/-- Containment in the edge finset of the all-incompatible system's graph is
containment in the edge finset of the complete graph (stated as an `iff` so
it applies whatever `Fintype` instance the goal carries). -/
private lemma subset_completeSystem_edgeFinset_iff {m : ℕ} (X : Fin m → Unit)
    [Fintype (incompGraph completeSystem X).edgeSet]
    (E : Finset (Sym2 (Fin m))) :
    E ⊆ (incompGraph completeSystem X).edgeFinset ↔
      E ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset := by
  constructor
  · intro h e he
    have h2 := h he
    rw [SimpleGraph.mem_edgeFinset] at h2 ⊢
    revert h2
    refine Sym2.ind (fun a b => ?_) e
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet, incompGraph_adj,
      SimpleGraph.top_adj]
    intro hadj
    exact hadj.1
  · intro h e he
    have h2 := h he
    rw [SimpleGraph.mem_edgeFinset] at h2 ⊢
    revert h2
    refine Sym2.ind (fun a b => ?_) e
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet, incompGraph_adj,
      SimpleGraph.top_adj]
    intro hne
    exact ⟨hne, trivial⟩

/-- The fiber over `S = univ` is the connected-spanning-subgraph sum, i.e.
the complete-graph Ursell value. -/
lemma fiber_univ (m : ℕ) :
    ∑ E ∈ (⊤ : SimpleGraph (Fin (m + 1))).edgeFinset.powerset.filter
        (fun E => reachSet m E = Finset.univ), (-1 : ℤ) ^ E.card
      = ursellComplete (m + 1) := by
  classical
  unfold ursellComplete ursell
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext E
  simp only [Finset.mem_filter, Finset.mem_powerset]
  rw [subset_completeSystem_edgeFinset_iff]
  exact and_congr Iff.rfl reachSet_eq_univ_iff

/-! ### The codimension-one fiber: relabeling along `Fin.succAbove` -/

section Relabel

variable {k : ℕ}

/-- Pulling a walk in the relabeled graph back along `Fin.succAbove v`:
every vertex visited lies in the image, and the endpoints are reachable in
the original graph. -/
private lemma walk_image_pullback (v : Fin (k + 2))
    (E : Finset (Sym2 (Fin (k + 1)))) {z y : Fin (k + 2)}
    (p : (fromEdgeSet (↑(E.image (Sym2.map v.succAbove)) :
        Set (Sym2 (Fin (k + 2))))).Walk z y) :
    ∀ a : Fin (k + 1), z = v.succAbove a →
      ∃ b : Fin (k + 1), y = v.succAbove b ∧
        (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 1))))).Reachable a b := by
  induction p with
  | nil =>
    intro a ha
    exact ⟨a, ha, SimpleGraph.Reachable.refl a⟩
  | @cons u c y hadj ptail ih =>
    intro a hz
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨hmem, hne⟩ := hadj
    rw [Finset.coe_image, Set.mem_image] at hmem
    obtain ⟨e, heE, hmap⟩ := hmem
    revert heE hmap
    refine Sym2.ind (fun x₁ x₂ => ?_) e
    intro heE hmap
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · -- s(ι x₁, ι x₂) = s(u, c) with ι x₁ = u, ι x₂ = c
      have hax : x₁ = a :=
        Fin.succAbove_right_injective (by rw [h₁, hz])
      subst hax
      have hadj_small :
          (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 1))))).Adj x₁ x₂ := by
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨heE, fun hcontra => hne ?_⟩
        rw [← h₁, ← h₂, hcontra]
      obtain ⟨b, hb, hr⟩ := ih x₂ h₂.symm
      exact ⟨b, hb, hadj_small.reachable.trans hr⟩
    · -- ι x₁ = c, ι x₂ = u
      have hax : x₂ = a :=
        Fin.succAbove_right_injective (by rw [h₂, hz])
      subst hax
      have hadj_small :
          (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 1))))).Adj x₂ x₁ := by
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨Sym2.eq_swap ▸ heE, fun hcontra => hne ?_⟩
        rw [← h₂, ← h₁, hcontra]
      obtain ⟨b, hb, hr⟩ := ih x₁ h₁.symm
      exact ⟨b, hb, hadj_small.reachable.trans hr⟩

/-- **Reachability transport** along the relabeling `Fin.succAbove v`. -/
private lemma reachable_image_iff (v : Fin (k + 2))
    (E : Finset (Sym2 (Fin (k + 1)))) (a b : Fin (k + 1)) :
    (fromEdgeSet (↑(E.image (Sym2.map v.succAbove)) :
        Set (Sym2 (Fin (k + 2))))).Reachable (v.succAbove a) (v.succAbove b) ↔
      (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 1))))).Reachable a b := by
  constructor
  · intro h
    obtain ⟨p⟩ := h
    obtain ⟨b', hb', hr⟩ := walk_image_pullback v E p a rfl
    have hbb : b = b' := Fin.succAbove_right_injective hb'
    rw [hbb]
    exact hr
  · intro h
    refine SimpleGraph.Reachable.map
      (⟨v.succAbove, ?_⟩ : (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 1))))) →g
        (fromEdgeSet (↑(E.image (Sym2.map v.succAbove)) :
          Set (Sym2 (Fin (k + 2)))))) h
    intro x y hxy
    rw [SimpleGraph.fromEdgeSet_adj] at hxy ⊢
    obtain ⟨hmem, hne'⟩ := hxy
    refine ⟨?_, fun hc => hne' (Fin.succAbove_right_injective hc)⟩
    rw [Finset.coe_image]
    exact ⟨s(x, y), hmem, by rw [Sym2.map_mk]⟩

/-- The deleted vertex `v` is isolated in the relabeled graph. -/
private lemma not_reachable_image_v (v : Fin (k + 2)) (hv : v ≠ 0)
    (E : Finset (Sym2 (Fin (k + 1)))) :
    ¬ (fromEdgeSet (↑(E.image (Sym2.map v.succAbove)) :
        Set (Sym2 (Fin (k + 2))))).Reachable 0 v := by
  intro h
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => exact hv rfl
  | cons hadj ptail =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨hmem, -⟩ := hadj
    rw [Finset.coe_image, Set.mem_image] at hmem
    obtain ⟨e, -, hmap⟩ := hmem
    revert hmap
    refine Sym2.ind (fun x₁ x₂ => ?_) e
    intro hmap
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    rcases hmap with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact Fin.succAbove_ne v x₁ h₁
    · exact Fin.succAbove_ne v x₂ h₂

/-- **Codimension-one fiber.**  The fiber over `S` with `0 ∈ S`,
`|S| = k + 1` (so `Sᶜ = {v}`, `v ≠ 0`) is in sign-preserving bijection with
the connected spanning subgraphs of `K_{k+1}`; it sums to `d(k+1)`. -/
lemma fiber_card_eq (k : ℕ) (S : Finset (Fin (k + 2)))
    (h0 : (0 : Fin (k + 2)) ∈ S) (hcard : S.card = k + 1) :
    ∑ E ∈ (⊤ : SimpleGraph (Fin (k + 2))).edgeFinset.powerset.filter
        (fun E => reachSet (k + 1) E = S), (-1 : ℤ) ^ E.card
      = ursellComplete (k + 1) := by
  classical
  -- extract the unique missing vertex
  have hcs : (Finset.univ \ S).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, hcard]
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcs
  have hvS : v ∉ S := by
    have hmem : v ∈ Finset.univ \ S := hv ▸ Finset.mem_singleton_self v
    exact (Finset.mem_sdiff.mp hmem).2
  have hv0 : v ≠ 0 := fun h => hvS (h ▸ h0)
  have hmemS : ∀ x : Fin (k + 2), x ∈ S ↔ x ≠ v := by
    intro x
    constructor
    · intro hx hxv
      exact hvS (hxv ▸ hx)
    · intro hxv
      by_contra hxS
      have hmem : x ∈ Finset.univ \ S :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
      rw [hv] at hmem
      exact hxv (Finset.mem_singleton.mp hmem)
  -- the fiber is the image of the small connected subgraphs
  have himg : (⊤ : SimpleGraph (Fin (k + 2))).edgeFinset.powerset.filter
        (fun E => reachSet (k + 1) E = S)
      = ((⊤ : SimpleGraph (Fin (k + 1))).edgeFinset.powerset.filter
          (fun E' : Finset (Sym2 (Fin (k + 1))) =>
            (fromEdgeSet (↑E' : Set (Sym2 (Fin (k + 1))))).Connected)).image
          (fun E' : Finset (Sym2 (Fin (k + 1))) =>
            E'.image (Sym2.map v.succAbove)) := by
    ext E
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hEsub, hreach⟩
      -- every edge of E avoids v
      have hedge : ∀ a b : Fin (k + 2), s(a, b) ∈ E → a ≠ v := by
        intro a b hab hcontra
        have hne : a ≠ b := by
          have hmem := hEsub hab
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            SimpleGraph.top_adj] at hmem
          exact hmem
        have hbv : b ≠ v := fun hbv => hne (hcontra.trans hbv.symm)
        have hbS : b ∈ S := (hmemS b).mpr hbv
        have hbR : (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 2))))).Reachable 0 b :=
          mem_reachSet.mp (hreach.symm ▸ hbS)
        have haR : (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 2))))).Reachable 0 a :=
          hbR.trans (SimpleGraph.Adj.reachable
            ((SimpleGraph.fromEdgeSet_adj _).mpr
              ⟨Finset.mem_coe.mpr (Sym2.eq_swap ▸ hab), hne.symm⟩))
        have haS : a ∈ S := hreach ▸ mem_reachSet.mpr haR
        exact ((hmemS a).mp haS) hcontra
      -- hence E lies in the image of the edge relabeling
      have hEimg : E ⊆ (Finset.univ : Finset (Sym2 (Fin (k + 1)))).image
          (Sym2.map v.succAbove) := by
        intro e he
        revert he
        refine Sym2.ind (fun a b => ?_) e
        intro he
        have ha : a ≠ v := hedge a b he
        have hb : b ≠ v := hedge b a (Sym2.eq_swap ▸ he)
        obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq ha
        obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hb
        rw [Finset.mem_image]
        exact ⟨s(a', b'), Finset.mem_univ _, by rw [Sym2.map_mk, ha', hb']⟩
      obtain ⟨E', hE'univ, hE'⟩ := Finset.subset_image_iff.mp hEimg
      refine ⟨E', ?_, hE'⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · -- E' consists of non-diagonal pairs
        intro e' he'
        have hmem : Sym2.map v.succAbove e' ∈ E :=
          hE' ▸ Finset.mem_image_of_mem _ he'
        have hnd := hEsub hmem
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
          Set.mem_compl_iff, Sym2.mem_diagSet] at hnd
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
          Set.mem_compl_iff, Sym2.mem_diagSet]
        intro hd
        exact hnd (Sym2.IsDiag.map hd)
      · -- fromEdgeSet E' is connected
        rw [SimpleGraph.connected_iff]
        refine ⟨fun a b => ?_, ⟨0⟩⟩
        have hra : (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 2))))).Reachable 0
            (v.succAbove a) := by
          apply mem_reachSet.mp
          have : v.succAbove a ∈ S := (hmemS _).mpr (Fin.succAbove_ne v a)
          rw [hreach]
          exact this
        have hrb : (fromEdgeSet (↑E : Set (Sym2 (Fin (k + 2))))).Reachable 0
            (v.succAbove b) := by
          apply mem_reachSet.mp
          have : v.succAbove b ∈ S := (hmemS _).mpr (Fin.succAbove_ne v b)
          rw [hreach]
          exact this
        have hab_big := hra.symm.trans hrb
        rw [← hE'] at hab_big
        exact (reachable_image_iff v E' a b).mp hab_big
    · rintro ⟨E', hE', rfl⟩
      rw [Finset.mem_filter, Finset.mem_powerset] at hE'
      obtain ⟨hE'sub, hconn⟩ := hE'
      constructor
      · -- the image consists of non-diagonal pairs
        intro e he
        rw [Finset.mem_image] at he
        obtain ⟨e', he', rfl⟩ := he
        have hnd := hE'sub he'
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
          Set.mem_compl_iff, Sym2.mem_diagSet] at hnd
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
          Set.mem_compl_iff, Sym2.mem_diagSet]
        intro hd
        exact hnd ((Sym2.isDiag_map Fin.succAbove_right_injective).mp hd)
      · -- the reachable set is exactly S
        ext x
        rw [mem_reachSet, hmemS x]
        constructor
        · intro hr hxv
          rw [hxv] at hr
          exact not_reachable_image_v v hv0 E' hr
        · intro hxv
          obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq hxv
          obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm hv0)
          have hr_small :
              (fromEdgeSet (↑E' : Set (Sym2 (Fin (k + 1))))).Reachable z x' :=
            hconn.preconnected z x'
          have hr_big := (reachable_image_iff v E' z x').mpr hr_small
          rw [hz, hx'] at hr_big
          exact hr_big
  -- sum over the image, transport the sign, identify with the Ursell value
  rw [himg, Finset.sum_image
    (fun E₁ _ E₂ _ h =>
      Finset.image_injective (Sym2.map.injective Fin.succAbove_right_injective) h)]
  have hsign : ∀ E' ∈ (⊤ : SimpleGraph (Fin (k + 1))).edgeFinset.powerset.filter
      (fun E' : Finset (Sym2 (Fin (k + 1))) =>
        (fromEdgeSet (↑E' : Set (Sym2 (Fin (k + 1))))).Connected),
      (-1 : ℤ) ^ (E'.image (Sym2.map v.succAbove)).card = (-1 : ℤ) ^ E'.card := by
    intro E' _
    rw [Finset.card_image_of_injective E'
      (Sym2.map.injective Fin.succAbove_right_injective)]
  rw [Finset.sum_congr rfl hsign]
  unfold ursellComplete ursell
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext E'
  simp only [Finset.mem_filter, Finset.mem_powerset]
  rw [subset_completeSystem_edgeFinset_iff]

end Relabel

/-! ### Counting the codimension-one fibers -/

/-- There are exactly `k + 1` sets `S ⊆ Fin (k+2)` with `0 ∈ S` and
`|S| = k + 1` (one per deleted vertex `v ≠ 0`). -/
private lemma card_codim_one_fibers (k : ℕ) :
    ((Finset.univ : Finset (Finset (Fin (k + 2)))).filter
        (fun S => (0 : Fin (k + 2)) ∈ S ∧ S.card = k + 1)).card = k + 1 := by
  classical
  have himg : (Finset.univ : Finset (Finset (Fin (k + 2)))).filter
        (fun S => (0 : Fin (k + 2)) ∈ S ∧ S.card = k + 1)
      = (Finset.univ.erase (0 : Fin (k + 2))).image
          (fun v => Finset.univ.erase v) := by
    ext S
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, h0, hcard⟩
      have hcs : (Finset.univ \ S).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Fintype.card_fin, hcard]
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcs
      have hvS : v ∉ S := by
        have hmem : v ∈ Finset.univ \ S := hv ▸ Finset.mem_singleton_self v
        exact (Finset.mem_sdiff.mp hmem).2
      have hv0 : v ≠ 0 := fun h => hvS (h ▸ h0)
      refine ⟨v, Finset.mem_erase.mpr ⟨hv0, Finset.mem_univ v⟩, ?_⟩
      ext x
      rw [Finset.mem_erase]
      constructor
      · rintro ⟨hxv, -⟩
        by_contra hxS
        have hmem : x ∈ Finset.univ \ S :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
        rw [hv] at hmem
        exact hxv (Finset.mem_singleton.mp hmem)
      · intro hxS
        exact ⟨fun hxv => hvS (hxv ▸ hxS), Finset.mem_univ x⟩
    · rintro ⟨v, hvmem, rfl⟩
      rw [Finset.mem_erase] at hvmem
      refine ⟨Finset.mem_univ _,
        Finset.mem_erase.mpr ⟨Ne.symm hvmem.1, Finset.mem_univ 0⟩, ?_⟩
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        Fintype.card_fin]
      omega
  have hinj : Set.InjOn (fun v : Fin (k + 2) => Finset.univ.erase v)
      ↑(Finset.univ.erase (0 : Fin (k + 2))) := by
    intro v _ w _ h
    have h' : Finset.univ.erase v = Finset.univ.erase w := h
    by_contra hne
    have hmem : v ∈ Finset.univ.erase w :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_univ v⟩
    rw [← h'] at hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  rw [himg, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem
    (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]
  omega

/-! ### The recurrence -/

/-- **T1 / Target A: the complete-graph Ursell recurrence.**
`d(n+1) = −n·d(n)` for `n ≥ 1`, by the component-of-vertex-0 decomposition of
the vanishing all-subgraphs signed sum on `K_{n+1}`.  This discharges the
`hrec` hypothesis of `ursellComplete_closed_form` (and through it, of the
single-polymer Mayer identity). -/
theorem ursellComplete_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ursellComplete (n + 1) = -(n : ℤ) * ursellComplete n := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- the all-subgraphs signed sum on K_{k+2} vanishes
  have hT : ∑ E ∈ (⊤ : SimpleGraph (Fin (k + 2))).edgeFinset.powerset,
      (-1 : ℤ) ^ E.card = 0 := by
    rw [allSubgraphs_signedSum]
    norm_num
  -- fiber it by the reachable set of vertex 0
  rw [← Finset.sum_fiberwise
    ((⊤ : SimpleGraph (Fin (k + 2))).edgeFinset.powerset)
    (fun E => reachSet (k + 1) E) (fun E => (-1 : ℤ) ^ E.card)] at hT
  -- evaluate each fiber
  have hpoint : ∀ S : Finset (Fin (k + 2)),
      (∑ E ∈ (⊤ : SimpleGraph (Fin (k + 2))).edgeFinset.powerset.filter
        (fun E => reachSet (k + 1) E = S), (-1 : ℤ) ^ E.card)
      = (if S = Finset.univ then ursellComplete (k + 2) else 0)
        + (if (0 : Fin (k + 2)) ∈ S ∧ S.card = k + 1
            then ursellComplete (k + 1) else 0) := by
    intro S
    by_cases h0 : (0 : Fin (k + 2)) ∈ S
    · by_cases huniv : S = Finset.univ
      · subst huniv
        rw [if_pos rfl, if_neg, add_zero]
        · exact fiber_univ (k + 1)
        · rintro ⟨-, hcard⟩
          rw [Finset.card_univ, Fintype.card_fin] at hcard
          omega
      · by_cases hcard : S.card = k + 1
        · rw [if_neg huniv, if_pos ⟨h0, hcard⟩, zero_add]
          exact fiber_card_eq k S h0 hcard
        · rw [if_neg huniv, if_neg (fun h => hcard h.2), add_zero]
          apply fiber_zero_of_small
          have hle : S.card ≤ k + 2 := by
            have h := Finset.card_le_univ S
            rwa [Fintype.card_fin] at h
          have hne2 : S.card ≠ k + 2 := by
            intro h
            apply huniv
            apply Finset.eq_univ_of_card
            rw [h, Fintype.card_fin]
          omega
    · rw [if_neg (fun h : S = Finset.univ => h0 (h.symm ▸ Finset.mem_univ 0)),
        if_neg (fun h : (0 : Fin (k + 2)) ∈ S ∧ S.card = k + 1 => h0 h.1),
        add_zero]
      exact fiber_zero_of_zero_notMem (k + 1) S h0
  simp only [hpoint] at hT
  rw [Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (Finset.univ : Finset (Fin (k + 2)))
      (fun _ => ursellComplete (k + 2)),
    if_pos (Finset.mem_univ _), ← Finset.sum_filter,
    Finset.sum_const, card_codim_one_fibers k] at hT
  -- hT : d(k+2) + (k+1) • d(k+1) = 0
  have hsmul : (k + 1) • ursellComplete (k + 1)
      = ((k : ℤ) + 1) * ursellComplete (k + 1) := by
    rw [nsmul_eq_mul]
    push_cast
    ring
  rw [hsmul] at hT
  show ursellComplete (k + 2) = -((k + 1 : ℕ) : ℤ) * ursellComplete (k + 1)
  push_cast
  linear_combination hT

/-! ### Target A and its consequences, now unconditional -/

/-- **Target A, unconditional:** the complete-graph Ursell closed form
`φ(K_{n+1}) = (−1)^n · n!`.  The recurrence hypothesis of
`ursellComplete_closed_form` is discharged by `ursellComplete_recurrence`. -/
theorem ursellComplete_eq (n : ℕ) :
    ursellComplete (n + 1) = (-1) ^ n * (Nat.factorial n : ℤ) :=
  ursellComplete_closed_form ursellComplete_recurrence n

/-- **Single-polymer cluster sum, unconditional:**
`clusterSum(singlePolymerSystem z) = log(1 + z)` for `‖z‖ < 1`. -/
theorem clusterSum_singlePolymer_eq_log (z : ℂ) (h : ‖z‖ < 1) :
    clusterSum (singlePolymerSystem z) = Complex.log (1 + z) :=
  clusterSum_singlePolymer z h ursellComplete_recurrence

/-- **Single-polymer Mayer identity, unconditional:** `Ξ = exp(clusterSum)`
for the one-polymer system with `‖z‖ < 1` — the `n = 1` case of the Mayer
cluster-expansion identity, with no remaining hypotheses. -/
theorem partition_singlePolymer_eq_exp (z : ℂ) (h : ‖z‖ < 1) :
    partition (singlePolymerSystem z)
        ({()} : Finset (singlePolymerSystem z).Polymer)
      = Complex.exp (clusterSum (singlePolymerSystem z)) :=
  partition_eq_exp_clusterSum_singlePolymer z h ursellComplete_recurrence

end YangMills.KP
