/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CubeLattice

/-!
# The modified metric `d_M(·, mod Ωᶜ)` — polymer-with-holes combinatorics
(gauge-RG, `hRpoly` campaign — brick P2b-i)

`docs/HRPOLY-CAMPAIGN-PLAN.md` brick **P2b-i**, `docs/BALABAN-SOURCE-BOUNDS.md`
§5.  Dimock II (arXiv:1212.5562) §3.1.2 defines, for the large-field region
`Ω_k` (complement `Ω_k^c`), the **modified metric** `d_M(X, mod Ω_k^c)` on
polymers (eq. 150): the minimal length of a continuum tree graph contained
in `X` that meets every `M`-cube of `X ∩ Ω_k`.  It *discounts* the
large-field cubes (paid for by the Gaussian suppression, not the cluster
weight), and is the geometric input of the with-holes summability (eq. 151)

    ∑_{X ⊇ □}  e^{−κ₀ d_M(X, mod Ω_k^c)}  ≤  K₀ ,

proved in **Lemma E.3** (Appendix E).  The full eq-151 result additionally
needs the holes' Gaussian suppression (P4, the months-scale fluctuation
integral; **NOT** here).  This file opens the **purely combinatorial core**
of Lemma E.3's proof.

## What this file proves (faithful, non-vacuous, oracle-clean)

* **`HoleFamily`** / **`polymerWithHoles`** — the Dimock eq-(149) substrate:
  a hole-component family `H`, and the predicate "`X` respects `H`" (each
  hole is either fully contained in `X` or disjoint from `X`).
* **`skeleton`** — the cubes of `X` lying in no hole (`X ∩ (⋃H)ᶜ`); the part
  of the polymer the discrete modified metric actually weights.
* **`cubeConnected`** — the walk-based form of "connected polymer".
* **`walk_crosses_frontier`** — the elementary bridge lemma: a walk that
  stays in `A ∪ B`, starts in `A \ B` and ends in `B \ A`, must cross an
  `Adj`-edge from `A` to `B`.
* **`absorbedHole_touches_skeleton_single`** and **`absorbedHole_touches_skeleton_multi`** —
  every absorbed hole in a connected polymer must touch the skeleton $Y$ via an edge.
* **`touchingHoles_card_le`** — the number of absorbed holes touching the skeleton $Y$ is at most $\Delta \cdot |Y|$.
* **`card_le_activeEdges_add_one`** — the active-edge cardinality bound for connected sets: $|S| \leq |E(G[S])| + 1$.
* **`discreteModifiedMetric`** — the discrete modified metric $d_M(X, \bmod H)$ defined as the Steiner tree length of the skeleton.
* **`skeleton_card_le_discreteModifiedMetric_add_one`** — the skeleton size is bounded by the discrete modified metric plus 1: $|Y| \leq d_M(X, \bmod H) + 1$.
* **`discreteModifiedMetric_empty_holes`** — when there are no holes, the metric reduces to $|X| - 1$.

## What is NOT here (honest scope)

* The full modified-metric summability under Gaussian suppression is **open** (requires P4, months-scale). Without the P4 large-field analytic suppression $e^{-c |H_0|}$, the sum over all polymers for a fixed skeleton can diverge.
* Everything is **lattice / finite-volume / φ⁴₃-combinatorics**.  Dimock's
  constants are `φ⁴₃`; the 4D YM activity bounds come from Bałaban's YM
  papers, not transcribed here.  Clay distance **~0% (<0.1%), unchanged**.

**Source.**  Dimock II (arXiv:1212.5562) §3.1.2 eqs. 149–151 and Appendix E
(Lemma E.3); strategy/framing Lluis Eriksson.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open Finset

namespace YangMills.RG

open SimpleGraph

/-- The `d`-dimensional cube type on the `L`-torus. -/
abbrev Cube (d L : ℕ) := Fin d → ZMod L

/-- A **hole-component family** (Dimock II §3.1.2): a finite set of finite
sets of cubes — the connected components `Ω_{k,α}^c` of the large-field
region `Ω_k^c`.  Carried abstractly; no disjointness/connectedness assumed
here (they are hypotheses of the bounds that need them). -/
structure HoleFamily (d L : ℕ) where
  /-- The collection of hole-components, each a finite set of cubes. -/
  holes : Finset (Finset (Cube d L))

/-- **Dimock eq. (149) — the polymer-with-holes predicate.**  A finite cube
set `X` *respects* the hole family `H` iff every hole-component `H₀ ∈ H.holes`
is either fully contained in `X` or disjoint from `X`.  This is the defining
condition of the polymer class `𝓓_k(mod Ω_k^c)`: the cluster expansion
"sees" each large-field component as an atomic unit. -/
def polymerWithHoles {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) : Prop :=
  ∀ H₀ ∈ H.holes, H₀ ⊆ X ∨ Disjoint H₀ X

/-- **Complement-skeleton**: the cubes of `X` lying in *no* hole, i.e.
`X ∩ (⋃H.holes)ᶜ`.  This is the part of the polymer the modified metric
`d_M` actually weights; the cubes inside holes are discounted. -/
def skeleton {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) : Finset (Cube d L) :=
  X.filter (fun z => ¬ ∃ H₀ ∈ H.holes, z ∈ H₀)

/-- The skeleton is part of `X`. -/
lemma skeleton_subset {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) :
    skeleton H X ⊆ X := by
  intro z hz
  simp only [skeleton, mem_filter] at hz
  exact hz.1

/-- A set of vertices `S` is **walk-connected** in a graph `G`. -/
def walkConnected {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ w : G.Walk x y, ∀ v ∈ w.support, v ∈ S

/-- There are no adjacency edges between different holes in the hole collection. -/
def noEdgesBetweenHoles {V : Type*} (G : SimpleGraph V) (holes : Finset (Finset V)) : Prop :=
  ∀ H₁ ∈ holes, ∀ H₂ ∈ holes, H₁ ≠ H₂ → ∀ x ∈ H₁, ∀ y ∈ H₂, ¬ G.Adj x y

/-- A cube-set `S` is **walk-connected** in `cubeAdj` (the walk-based form of
connectivity used throughout `RG/AnimalTour.lean`): every vertex of `S` is
reachable from every other by a `cubeAdj`-walk staying inside `S`.  This is
the self-contained form of "connected polymer" avoiding the `Set`-vs-`Finset`
`SimpleGraph.Connected` API. -/
def cubeConnected {d L : ℕ} (S : Finset (Cube d L)) : Prop :=
  walkConnected (cubeAdj d L) S

/-- **Walk-bridge lemma (the elementary frontier-edge argument).**  If a walk
from `z` to `w` stays inside `A ∪ B`, starts at `z ∈ A \ B` and ends at
`w ∈ B \ A`, then some edge of the walk crosses from `A` to `B`: there is an
`Adj`-edge `a—b` with `a ∈ A`, `b ∈ B`.  Proved by induction on the walk: at
`cons h p'`, if the head successor is in `B`, the head edge is the witness;
otherwise recurse on the tail.  This is the self-contained core behind
connectivity forcing a frontier edge. -/
lemma walk_crosses_frontier {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) {z w : V} (p : G.Walk z w)
    (hp : ∀ v ∈ p.support, v ∈ A ∪ B)
    (hzA : z ∈ A) (hzB : z ∉ B) (hwB : w ∈ B) (hwA : w ∉ A) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  generalize hn : p.length = n
  induction n using Nat.strongRecOn generalizing z p hzA hzB hp with
  | ind n ih =>
    match p with
    | Walk.nil =>
      exfalso
      exact hwA hzA
    | @Walk.cons _ _ _ v _ h p' =>
      have hvsupp : v ∈ (Walk.cons h p').support :=
        List.mem_cons_of_mem z (Walk.start_mem_support p')
      have hv : v ∈ A ∪ B := hp v hvsupp
      rcases mem_union.mp hv with hvA | hvB
      · by_cases hvB' : v ∈ B
        · exact ⟨z, hzA, v, hvB', h⟩
        · apply ih p'.length (by rw [← hn, Walk.length_cons]; omega) p' (fun y hy => hp y (List.mem_cons_of_mem z hy)) hvA hvB' rfl
      · exact ⟨z, hzA, v, hvB, h⟩

/-- **Absorbed-hole touching (single-hole case) — the combinatorial heart of
Dimock Lemma E.3.**  Suppose `X = Y ∪ H₀` (skeleton `Y`, single absorbed hole
`H₀`), `X` is `cubeConnected`, both `Y` and `H₀` nonempty and disjoint.  Then
`H₀` touches `Y`: there exist `z ∈ H₀`, `w ∈ Y` with `cubeAdj`-adjacent.

Equivalently, the hole-frontier of `Y` is nonempty.  Proof: walk-connectivity
gives a `cubeAdj`-walk inside `X` from `z ∈ H₀` to `w ∈ Y`; the
`walk_crosses_frontier` lemma extracts a `cubeAdj`-edge `H₀ → Y`.  This is
exactly the step by which Dimock bounds the number of absorbable holes by the
per-cube frontier of the skeleton, turning a hole-discounted decay into a
uniform polymer count. -/
theorem absorbedHole_touches_skeleton_single {d L : ℕ} [NeZero L]
    (Y H₀ : Finset (Cube d L)) (hdisj : Disjoint Y H₀)
    (hYne : Y.Nonempty) (hH₀ne : H₀.Nonempty)
    (hconn : cubeConnected (Y ∪ H₀)) :
    ∃ z ∈ H₀, ∃ w ∈ Y, (cubeAdj d L).Adj z w := by
  obtain ⟨z, hz⟩ := hH₀ne
  obtain ⟨w, hw⟩ := hYne
  have hzX : z ∈ Y ∪ H₀ := Finset.mem_union.mpr (Or.inr hz)
  have hwX : w ∈ Y ∪ H₀ := Finset.mem_union.mpr (Or.inl hw)
  obtain ⟨p, hp⟩ := hconn z hzX w hwX
  -- Disjoint Y H₀ ⟹ z ∈ H₀ ∉ Y, w ∈ Y ∉ H₀.
  have hdj : ∀ a ∈ Y, ∀ b ∈ H₀, a ≠ b := Finset.disjoint_iff_ne.mp hdisj
  have hznotY : z ∉ Y := fun h => absurd rfl (hdj z h z hz)
  have hwH₀ : w ∉ H₀ := fun h => absurd rfl (hdj w hw w h)
  -- hp : v ∈ Y ∪ H₀; rewrite to v ∈ H₀ ∪ Y to match the frontier lemma.
  have hp' : ∀ v ∈ p.support, v ∈ H₀ ∪ Y := fun v hv =>
    (Finset.mem_union.mpr (Finset.mem_union.mp (hp v hv)).symm)
  have hzX' : z ∈ H₀ ∪ Y := Finset.mem_union.mpr (Or.inl hz)
  have hwX' : w ∈ H₀ ∪ Y := Finset.mem_union.mpr (Or.inr hw)
  obtain ⟨a, haH₀, b, hbY, hab⟩ :=
    walk_crosses_frontier (cubeAdj d L) H₀ Y p hp' hz hznotY hw hwH₀
  exact ⟨a, haH₀, b, hbY, hab⟩

/-- **Absorbed-hole touching (multi-hole case) — extension of Dimock Appendix E Lemma E.3.**
If a polymer is connected and contains a set of disjoint holes with no edges between them,
then every absorbed hole must touch the skeleton. -/
theorem absorbedHole_touches_skeleton_multi {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (Y : Finset V) (holes : Finset (Finset V)) (H_absorbed : Finset (Finset V))
    (hsub : H_absorbed ⊆ holes)
    (hnoedges : noEdgesBetweenHoles G holes)
    (hdisj_Y : ∀ H₀ ∈ H_absorbed, Disjoint Y H₀)
    (hYne : Y.Nonempty) (H₀ : Finset V) (hH₀mem : H₀ ∈ H_absorbed) (hH₀ne : H₀.Nonempty)
    (hconn : walkConnected G (Y ∪ H_absorbed.biUnion id)) :
    ∃ z ∈ H₀, ∃ w ∈ Y, G.Adj z w := by
  obtain ⟨z, hz⟩ := hH₀ne
  obtain ⟨w, hw⟩ := hYne
  have hzX : z ∈ Y ∪ H_absorbed.biUnion id := by
    apply Finset.mem_union.mpr
    right
    rw [Finset.mem_biUnion]
    exact ⟨H₀, hH₀mem, hz⟩
  have hwX : w ∈ Y ∪ H_absorbed.biUnion id := by
    apply Finset.mem_union.mpr
    left
    exact hw
  obtain ⟨p, hp⟩ := hconn z hzX w hwX
  let B := (Y ∪ H_absorbed.biUnion id) \ H₀
  have hzA : z ∈ H₀ := hz
  have hzB : z ∉ B := by
    intro h
    rw [Finset.mem_sdiff] at h
    exact h.2 hz
  have hwB : w ∈ B := by
    rw [Finset.mem_sdiff]
    refine ⟨hwX, ?_⟩
    intro hwH₀
    have hdj := Finset.disjoint_iff_ne.mp (hdisj_Y H₀ hH₀mem)
    exact absurd rfl (hdj w hw w hwH₀)
  have hwA : w ∉ H₀ := by
    intro h
    have hdj := Finset.disjoint_iff_ne.mp (hdisj_Y H₀ hH₀mem)
    exact absurd rfl (hdj w hw w h)
  have hAB_eq : H₀ ∪ B = Y ∪ H_absorbed.biUnion id := by
    ext x
    simp only [B, Finset.mem_union, Finset.mem_sdiff, Finset.mem_biUnion, id_eq]
    by_cases hx : x ∈ H₀
    · simp only [hx, true_or, not_true, and_false, true_iff]
      right
      exact ⟨H₀, hH₀mem, hx⟩
    · simp only [hx, false_or, not_false_iff, and_true]
  have hpB : ∀ v ∈ p.support, v ∈ H₀ ∪ B := by
    intro v hv
    rw [hAB_eq]
    exact hp v hv
  obtain ⟨a, haH₀, b, hbB, hab⟩ := walk_crosses_frontier G H₀ B p hpB hzA hzB hwB hwA
  rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion] at hbB
  rcases hbB.1 with hbY | ⟨H₁, hH₁mem, hbH₁⟩
  · exact ⟨a, haH₀, b, hbY, hab⟩
  · have hneq : H₀ ≠ H₁ := by
      rintro rfl
      exact hbB.2 hbH₁
    have hH₀holes : H₀ ∈ holes := hsub hH₀mem
    have hH₁holes : H₁ ∈ holes := hsub hH₁mem
    have hno := hnoedges H₀ hH₀holes H₁ hH₁holes hneq a haH₀ b hbH₁
    exfalso
    exact hno hab

/-- The set of holes absorbed by a polymer `X`. -/
def absorbedHoles {V : Type*} [DecidableEq V] (holes : Finset (Finset V)) (X : Finset V) : Finset (Finset V) :=
  holes.filter (· ⊆ X)

/-- If `X` respects the hole family, it is the union of the skeleton and the absorbed holes. -/
lemma eq_union_absorbed {V : Type*} [DecidableEq V] (holes : Finset (Finset V)) (X : Finset V)
    (hresp : ∀ H₀ ∈ holes, H₀ ⊆ X ∨ Disjoint H₀ X) :
    X = (X.filter (fun z => ¬ ∃ H₀ ∈ holes, z ∈ H₀)) ∪ (absorbedHoles holes X).biUnion id := by
  ext x
  simp only [absorbedHoles, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, id_eq]
  constructor
  · intro hxX
    by_cases hxH : ∃ H₀ ∈ holes, x ∈ H₀
    · right
      rcases hxH with ⟨H₀, hH₀, hxH₀⟩
      refine ⟨H₀, ⟨hH₀, ?_⟩, hxH₀⟩
      have hresp₀ := hresp H₀ hH₀
      rcases hresp₀ with hsub | hdj
      · exact hsub
      · have h_not_dj : ¬ Disjoint H₀ X := by
          rw [disjoint_iff_ne]
          push_neg
          exact ⟨x, hxH₀, x, hxX, rfl⟩
        exact absurd hdj h_not_dj
    · left
      refine ⟨hxX, hxH⟩
  · rintro (⟨hxX, _⟩ | ⟨H₀, ⟨_, hsub⟩, hxH₀⟩)
    · exact hxX
    · exact hsub hxH₀

/-- The holes in `holes` that touch the skeleton `Y` via a graph edge. -/
def touchingHoles {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V)
    (holes : Finset (Finset V)) : Finset (Finset V) :=
  holes.filter (fun (H₀ : Finset V) => ∃ z ∈ H₀, ∃ w ∈ Y, G.Adj z w)

/-- Every absorbed hole in a connected polymer must touch the skeleton. -/
lemma absorbed_subset_touching {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (holes : Finset (Finset V)) (X : Finset V)
    (hresp : ∀ H₀ ∈ holes, H₀ ⊆ X ∨ Disjoint H₀ X)
    (hskel : Y = X.filter (fun z => ¬ ∃ H₀ ∈ holes, z ∈ H₀))
    (hnoedges : noEdgesBetweenHoles G holes)
    (hdisj_Y : ∀ H₀ ∈ holes, Disjoint Y H₀)
    (hYne : Y.Nonempty) (hholes_ne : ∀ H₀ ∈ holes, H₀.Nonempty)
    (hconn : walkConnected G X) :
    absorbedHoles holes X ⊆ touchingHoles G Y holes := by
  intro H₀ hH₀
  rw [absorbedHoles] at hH₀
  have hH₀' : H₀ ∈ holes.filter (· ⊆ X) := hH₀
  rw [mem_filter] at hH₀'
  rw [touchingHoles, mem_filter]
  refine ⟨hH₀'.1, ?_⟩
  have hH₀ne : H₀.Nonempty := hholes_ne H₀ hH₀'.1
  have hsub : absorbedHoles holes X ⊆ holes := by
    intro H hH
    rw [absorbedHoles] at hH
    exact (mem_filter.mp hH).1
  have hH₀mem : H₀ ∈ absorbedHoles holes X := hH₀
  have hX_eq : X = Y ∪ (absorbedHoles holes X).biUnion id := by
    rw [hskel]
    exact eq_union_absorbed holes X hresp
  have hconn_eq : walkConnected G (Y ∪ (absorbedHoles holes X).biUnion id) := by
    rw [← hX_eq]
    exact hconn
  have hdisj_Y' : ∀ H ∈ absorbedHoles holes X, Disjoint Y H := by
    intro H hH
    exact hdisj_Y H (hsub hH)
  exact absorbedHole_touches_skeleton_multi G Y holes (absorbedHoles holes X) hsub hnoedges hdisj_Y' hYne H₀ hH₀mem hH₀ne hconn_eq

/-- The neighbor pairs of a set `Y` in `G`. -/
def neighborPairs {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) : Finset (V × V) :=
  Y.biUnion (fun w => (G.neighborSet w).toFinset.map ⟨fun z => (w, z), fun _ _ h => by injection h⟩)

lemma card_neighborPairs {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) :
    (neighborPairs G Y).card = ∑ w ∈ Y, G.degree w := by
  rw [neighborPairs, card_biUnion]
  · simp only [card_map, Set.toFinset_card, card_neighborSet_eq_degree]
  · intro x hx y hy hne
    dsimp [Function.onFun]
    rw [disjoint_iff_ne]
    rintro ⟨x1, x2⟩ hx' ⟨y1, y2⟩ hy' h
    simp only [mem_map, Set.mem_toFinset, Function.Embedding.coeFn_mk] at hx' hy'
    obtain ⟨a, ha, hx_eq⟩ := hx'
    obtain ⟨b, hb, hy_eq⟩ := hy'
    injection hx_eq with hx1 _
    injection hy_eq with hy1 _
    injection h with h1 _
    have h_xy : x = y := by
      rw [hx1, h1, ← hy1]
    exact hne h_xy

/-- **Multiplicity Bound (the combinatorial crux of Dimock Lemma E.3).**
The number of holes that touch `Y` is at most `Δ * |Y|`. Since the holes are disjoint,
the map from `touchingHoles` to `neighborPairs` is injective, yielding the bound. -/
theorem touchingHoles_card_le {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (holes : Finset (Finset V)) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hdisj : ∀ H₁ ∈ holes, ∀ H₂ ∈ holes, H₁ ≠ H₂ → Disjoint H₁ H₂) :
    (touchingHoles G Y holes).card ≤ Δ * Y.card := by
  classical
  by_cases hV : Nonempty V
  · have : Inhabited (V × V) := ⟨(Classical.choice hV, Classical.choice hV)⟩
    let f (H₀ : Finset V) : V × V :=
      if h : ∃ (wz : V × V), wz.1 ∈ Y ∧ wz.2 ∈ H₀ ∧ G.Adj wz.2 wz.1 then
        Classical.choose h
      else default
    have h_inj : ∀ H₁ ∈ touchingHoles G Y holes, ∀ H₂ ∈ touchingHoles G Y holes, f H₁ = f H₂ → H₁ = H₂ := by
      intro H₁ hH₁ H₂ hH₂ hf
      rw [touchingHoles, mem_filter] at hH₁ hH₂
      have h1 : ∃ (wz : V × V), wz.1 ∈ Y ∧ wz.2 ∈ H₁ ∧ G.Adj wz.2 wz.1 := by
        rcases hH₁.2 with ⟨z, hz, w, hw, hadj⟩
        exact ⟨(w, z), hw, hz, hadj⟩
      have h2 : ∃ (wz : V × V), wz.1 ∈ Y ∧ wz.2 ∈ H₂ ∧ G.Adj wz.2 wz.1 := by
        rcases hH₂.2 with ⟨z, hz, w, hw, hadj⟩
        exact ⟨(w, z), hw, hz, hadj⟩
      have hf1 : f H₁ = Classical.choose h1 := dif_pos h1
      have hf2 : f H₂ = Classical.choose h2 := dif_pos h2
      rw [hf1, hf2] at hf
      have hc1 := Classical.choose_spec h1
      have hc2 := Classical.choose_spec h2
      have h_same : (Classical.choose h1).2 = (Classical.choose h2).2 := by
        congr 1
      have h_in_H₂ : (Classical.choose h1).2 ∈ H₂ := by
        rw [h_same]
        exact hc2.2.1
      by_contra h_ne
      have h_dj := hdisj H₁ hH₁.1 H₂ hH₂.1 h_ne
      rw [disjoint_iff_ne] at h_dj
      exact h_dj _ hc1.2.1 _ h_in_H₂ rfl
    have h_maps : ∀ H₀ ∈ touchingHoles G Y holes, f H₀ ∈ neighborPairs G Y := by
      intro H₀ hH₀
      rw [touchingHoles, mem_filter] at hH₀
      have h1 : ∃ (wz : V × V), wz.1 ∈ Y ∧ wz.2 ∈ H₀ ∧ G.Adj wz.2 wz.1 := by
        rcases hH₀.2 with ⟨z, hz, w, hw, hadj⟩
        exact ⟨(w, z), hw, hz, hadj⟩
      have hf1 : f H₀ = Classical.choose h1 := dif_pos h1
      rw [hf1]
      have hc := Classical.choose_spec h1
      rw [neighborPairs, mem_biUnion]
      refine ⟨(Classical.choose h1).1, hc.1, ?_⟩
      rw [mem_map]
      refine ⟨(Classical.choose h1).2, ?_, ?_⟩
      · rw [Set.mem_toFinset]
        exact hc.2.2.symm
      · rfl
    have h_le := Finset.card_le_card_of_injOn f h_maps h_inj
    have h_card := card_neighborPairs G Y
    have h_sum : ∑ w ∈ Y, G.degree w ≤ Δ * Y.card := by
      calc ∑ w ∈ Y, G.degree w
        _ ≤ ∑ w ∈ Y, Δ := sum_le_sum (fun w _ => hdeg w)
        _ = Y.card * Δ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
        _ = Δ * Y.card := by rw [mul_comm]
    omega
  · have h_empty : touchingHoles G Y holes = ∅ := by
      ext H₀
      rw [touchingHoles, mem_filter]
      simp
      rintro _ x
      exact (hV ⟨x⟩).elim
    rw [h_empty, card_empty]
    omega


lemma mem_of_mem_tail {α : Type*} {x : α} {l : List α} (h : x ∈ l.tail) : x ∈ l := by
  cases l with
  | nil => cases h
  | cons hd tl => exact List.mem_cons_of_mem hd h

lemma walkConnected_of_walk_from_root {V : Type*} (G : SimpleGraph V) (S : Finset V) (r : V)
    (h : ∀ x ∈ S, ∃ w : G.Walk r x, ∀ y ∈ w.support, y ∈ S) :
    walkConnected G S := by
  intro x hx y hy
  obtain ⟨wx, hwx⟩ := h x hx
  obtain ⟨wy, hwy⟩ := h y hy
  refine ⟨wx.reverse.append wy, ?_⟩
  intro v hv
  rw [Walk.support_append, List.mem_append, Walk.support_reverse] at hv
  rcases hv with hv | hv
  · rw [List.mem_reverse] at hv
    exact hwx v hv
  · have hv' : v ∈ wy.support := mem_of_mem_tail hv
    exact hwy v hv'

/-- The active edges of `G` with both endpoints in `S`. -/
def activeEdges {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)

lemma card_le_activeEdges_add_one_of_card {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (S : Finset V) (hconn : walkConnected G S) (hne : S.Nonempty) (hcard : S.card = n) :
    S.card ≤ (activeEdges G S).card + 1 := by
  induction n generalizing S with
  | zero =>
    omega
  | succ n ih =>
    by_cases hn : S.card = 1
    · omega
    · have h_gt : 2 ≤ S.card := by omega
      obtain ⟨r, hr⟩ := hne
      have hconn_root : ∀ x ∈ S, ∃ w : G.Walk r x, ∀ y ∈ w.support, y ∈ S := by
        intro x hx
        exact hconn r hr x hx
      obtain ⟨u, huS, hune, hS'conn, p, hp, hp_adj⟩ := exists_peel S hr h_gt hconn_root
      let S' := S.erase u
      have hS'ne : S'.Nonempty := by
        use r
        rw [mem_erase]
        exact ⟨hune.symm, hr⟩
      have hS'card : S'.card = n := by
        rw [card_erase_of_mem huS, hcard]
        omega
      have hS'conn_wc : walkConnected G S' := by
        refine walkConnected_of_walk_from_root G S' r ?_
        · intro x hx
          exact hS'conn x hx
      have ih_S' := ih S' hS'conn_wc hS'ne hS'card
      have h_subset : activeEdges G S' ⊆ activeEdges G S := by
        intro e he
        rw [activeEdges, mem_filter] at he ⊢
        refine ⟨he.1, ?_⟩
        intro v hv
        have := he.2 v hv
        exact mem_of_mem_erase this
      have h_strict : activeEdges G S' ⊂ activeEdges G S := by
        rw [ssubset_iff_of_subset h_subset]
        let e := s(p, u)
        have he_edge : e ∈ G.edgeFinset := by
          rw [mem_edgeFinset]
          exact hp_adj
        have he_S : e ∈ activeEdges G S := by
          unfold activeEdges; rw [mem_filter]
          refine ⟨he_edge, ?_⟩
          intro v hv
          rw [Sym2.mem_iff] at hv
          rcases hv with rfl | rfl
          · exact mem_of_mem_erase hp
          · exact huS
        have he_not_S' : e ∉ activeEdges G S' := by
          unfold activeEdges; rw [mem_filter]
          push_neg
          intro _
          use u
          refine ⟨?_, ?_⟩
          · rw [Sym2.mem_iff]
            right
            rfl
          · rw [mem_erase]
            push_neg
            intro h
            contradiction
        exact ⟨e, he_S, he_not_S'⟩
      have h_card_strict : (activeEdges G S').card < (activeEdges G S).card :=
        card_lt_card h_strict
      have h_card_erase : S'.card = S.card - 1 := card_erase_of_mem huS
      have h_S_card : S.card = S'.card + 1 := by omega
      omega

/-- For any connected vertex set `S`, its cardinality is bounded by the number of active edges plus 1. -/
theorem card_le_activeEdges_add_one {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hconn : walkConnected G S) (hne : S.Nonempty) :
    S.card ≤ (activeEdges G S).card + 1 :=
  card_le_activeEdges_add_one_of_card G S.card S hconn hne rfl

/-- The discrete modified metric d_M(X, mod H) defined as the Steiner tree length of the skeleton in G[X]. -/
noncomputable def discreteModifiedMetric {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) : ℕ := by
  classical
  let Y := skeleton H X
  exact if h : ∃ S : Finset (Cube d L), Y ⊆ S ∧ S ⊆ X ∧ cubeConnected S then
    sInf {n | ∃ S : Finset (Cube d L), Y ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n}
  else
    0

theorem skeleton_card_le_discreteModifiedMetric_add_one {d L : ℕ} (H : HoleFamily d L)
    (X : Finset (Cube d L)) (hconn : cubeConnected X) :
    (skeleton H X).card ≤ discreteModifiedMetric H X + 1 := by
  classical
  have h_ex : ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S := by
    refine ⟨X, skeleton_subset H X, by rfl, hconn⟩
  have h_metric : discreteModifiedMetric H X = sInf {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex]
  have h_ne : {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n}.Nonempty := by
    refine ⟨X.card - 1, X, skeleton_subset H X, by rfl, hconn, rfl⟩
  have h_mem := Nat.sInf_mem h_ne
  rw [← h_metric] at h_mem
  rcases h_mem with ⟨S, hY, _, _, hS_card⟩
  by_cases hS : S.card = 0
  · have hY_empty : skeleton H X = ∅ := by
      rw [card_eq_zero] at hS
      exact subset_empty.mp (hS ▸ hY)
    rw [hY_empty, card_empty]
    omega
  · have hS_pos : 1 ≤ S.card := by omega
    have h_le : (skeleton H X).card ≤ S.card := card_le_card hY
    omega

theorem discreteModifiedMetric_empty_holes {d L : ℕ} (H : HoleFamily d L) (hH : H.holes = ∅)
    (X : Finset (Cube d L)) (hconn : cubeConnected X) :
    discreteModifiedMetric H X = X.card - 1 := by
  classical
  have hY : skeleton H X = X := by
    unfold skeleton
    rw [hH]
    ext z
    simp
  have h_ex : ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S := by
    refine ⟨X, by rw [hY], by rfl, hconn⟩
  have h_metric : discreteModifiedMetric H X = sInf {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex]
  rw [h_metric]
  have h_eq : {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} = {X.card - 1} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨S, hS1, hS2, _, rfl⟩
      rw [hY] at hS1
      have : S = X := by exact subset_antisymm hS2 hS1
      rw [this]
    · rintro rfl
      refine ⟨X, by rw [hY], by rfl, hconn, rfl⟩
  rw [h_eq]
  have h_mem : sInf ({X.card - 1} : Set ℕ) ∈ ({X.card - 1} : Set ℕ) := Nat.sInf_mem ⟨X.card - 1, Set.mem_singleton _⟩
  exact Set.mem_singleton_iff.mp h_mem

/-- The family of connected, hole-respecting polymers with skeleton Y. -/
noncomputable def admissibleFillings {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (holes : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun X =>
    walkConnected G X ∧
    (∀ H₀ ∈ holes, H₀ ⊆ X ∨ Disjoint H₀ X) ∧
    X.filter (fun z => ¬ ∃ H₀ ∈ holes, z ∈ H₀) = Y)

lemma skeleton_disjoint_absorbed {V : Type*} [DecidableEq V] (holes : Finset (Finset V)) (X : Finset V)
    (H₀ : Finset V) (hH₀ : H₀ ∈ absorbedHoles holes X) :
    Disjoint (X.filter (fun z => ¬ ∃ H₀ ∈ holes, z ∈ H₀)) H₀ := by
  rw [disjoint_iff_ne]
  rintro x hx y hy rfl
  rw [mem_filter] at hx
  apply hx.2
  exact ⟨H₀, (mem_filter.mp hH₀).1, hy⟩

lemma admissibleFillings_inj {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (holes : Finset (Finset V)) (X₁ X₂ : Finset V)
    (hX₁ : X₁ ∈ admissibleFillings G Y holes) (hX₂ : X₂ ∈ admissibleFillings G Y holes)
    (h_eq : absorbedHoles holes X₁ = absorbedHoles holes X₂) :
    X₁ = X₂ := by
  classical
  rw [admissibleFillings, mem_filter] at hX₁ hX₂
  have h_eq1 := eq_union_absorbed holes X₁ hX₁.2.2.1
  have h_eq2 := eq_union_absorbed holes X₂ hX₂.2.2.1
  rw [hX₁.2.2.2] at h_eq1
  rw [hX₂.2.2.2] at h_eq2
  rw [h_eq1, h_eq2, h_eq]

/-- **Multi-hole Polymer Multiplicity Bound** (Dimock Appendix E, Lemma E.3).
    The number of connected, hole-respecting polymers X with a fixed skeleton Y
    is bounded by 2^(Δ * |Y|). -/
theorem fillings_card_le_two_pow {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (holes : Finset (Finset V)) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hdisj : ∀ H₁ ∈ holes, ∀ H₂ ∈ holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles G holes)
    (hYne : Y.Nonempty)
    (hholes_ne : ∀ H₀ ∈ holes, H₀.Nonempty) :
    (admissibleFillings G Y holes).card ≤ 2 ^ (Δ * Y.card) := by
  classical
  have h_maps : ∀ X ∈ admissibleFillings G Y holes, absorbedHoles holes X ∈ (touchingHoles G Y holes).powerset := by
    intro X hX
    rw [mem_powerset]
    have hX_mem := hX
    rw [admissibleFillings, mem_filter] at hX
    have hdisj_Y : ∀ H₀ ∈ holes, Disjoint Y H₀ := by
      intro H₀ hH₀
      rw [disjoint_iff_ne]
      rintro x hx y hy rfl
      rw [← hX.2.2.2, mem_filter] at hx
      apply hx.2
      exact ⟨H₀, hH₀, hy⟩
    exact absorbed_subset_touching G Y holes X hX.2.2.1 hX.2.2.2.symm hnoedges hdisj_Y hYne hholes_ne hX.2.1
  have h_inj : ∀ X₁ ∈ admissibleFillings G Y holes, ∀ X₂ ∈ admissibleFillings G Y holes,
      absorbedHoles holes X₁ = absorbedHoles holes X₂ → X₁ = X₂ := by
    intro X₁ hX₁ X₂ hX₂ h_eq
    exact admissibleFillings_inj G Y holes X₁ X₂ hX₁ hX₂ h_eq
  have h_le := card_le_card_of_injOn (fun X => absorbedHoles holes X) h_maps h_inj
  rw [card_powerset] at h_le
  have h_th := touchingHoles_card_le G Y holes Δ hdeg hdisj
  have h_pow : 2 ^ (touchingHoles G Y holes).card ≤ 2 ^ (Δ * Y.card) :=
    Nat.pow_le_pow_right (by decide) h_th
  exact h_le.trans h_pow

/-- The polymer multiplicity bound on the cube lattice. -/
theorem cube_fillings_card_le_two_pow (d L : ℕ) [NeZero L] (Y : Finset (Cube d L))
    (H : HoleFamily d L) (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hYne : Y.Nonempty)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty) :
    (admissibleFillings (cubeAdj d L) Y H.holes).card ≤ 2 ^ (3 ^ d * Y.card) :=
  fillings_card_le_two_pow (cubeAdj d L) Y H.holes (3 ^ d) (fun x => cubeAdj_degree_le d L x) hdisj hnoedges hYne hholes_ne

/-- The discrete modified metric is bounded above by the bulk tree length (card X - 1) for connected X. -/
theorem discreteModifiedMetric_le_bulkTreeLength {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L))
    (hconn : cubeConnected X) :
    discreteModifiedMetric H X ≤ X.card - 1 := by
  classical
  have h_ex : ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S :=
    ⟨X, skeleton_subset H X, by rfl, hconn⟩
  have h_met : discreteModifiedMetric H X = sInf {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex]
  rw [h_met]
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq]
  refine ⟨X, skeleton_subset H X, by rfl, hconn, rfl⟩

/-- Skeletal monotonicity of the discrete modified metric: a larger skeleton implies a larger metric. -/
theorem discreteModifiedMetric_mono_skeleton {d L : ℕ} (H₁ H₂ : HoleFamily d L) (X : Finset (Cube d L))
    (hskel : skeleton H₁ X ⊆ skeleton H₂ X) (hconn : cubeConnected X) :
    discreteModifiedMetric H₁ X ≤ discreteModifiedMetric H₂ X := by
  classical
  have h_ex₁ : ∃ S : Finset (Cube d L), skeleton H₁ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S :=
    ⟨X, skeleton_subset H₁ X, by rfl, hconn⟩
  have h_ex₂ : ∃ S : Finset (Cube d L), skeleton H₂ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S :=
    ⟨X, skeleton_subset H₂ X, by rfl, hconn⟩
  have h_met₁ : discreteModifiedMetric H₁ X = sInf {n | ∃ S : Finset (Cube d L), skeleton H₁ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex₁]
  have h_met₂ : discreteModifiedMetric H₂ X = sInf {n | ∃ S : Finset (Cube d L), skeleton H₂ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex₂]
  rw [h_met₁, h_met₂]
  have h_ne : {n | ∃ S : Finset (Cube d L), skeleton H₂ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n}.Nonempty :=
    ⟨X.card - 1, X, skeleton_subset H₂ X, by rfl, hconn, rfl⟩
  have h_mem := Nat.sInf_mem h_ne
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq] at h_mem ⊢
  rcases h_mem with ⟨S, hS_skel, hS_sub, hS_conn, h_eq⟩
  refine ⟨S, hskel.trans hS_skel, hS_sub, hS_conn, h_eq⟩

/-- Hole monotonicity of the discrete modified metric: more holes imply a smaller metric. -/
theorem discreteModifiedMetric_mono_holes {d L : ℕ} (H₁ H₂ : HoleFamily d L) (hH : H₁.holes ⊆ H₂.holes)
    (X : Finset (Cube d L)) (hconn : cubeConnected X) :
    discreteModifiedMetric H₂ X ≤ discreteModifiedMetric H₁ X := by
  classical
  have h_mono : skeleton H₂ X ⊆ skeleton H₁ X := by
    intro z hz
    simp only [skeleton, mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    intro ⟨H₀, hH₀, hzH₀⟩
    apply hz.2
    exact ⟨H₀, hH hH₀, hzH₀⟩
  have h_ex₁ : ∃ S : Finset (Cube d L), skeleton H₁ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S :=
    ⟨X, skeleton_subset H₁ X, by rfl, hconn⟩
  have h_ex₂ : ∃ S : Finset (Cube d L), skeleton H₂ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S :=
    ⟨X, skeleton_subset H₂ X, by rfl, hconn⟩
  have h_met₁ : discreteModifiedMetric H₁ X = sInf {n | ∃ S : Finset (Cube d L), skeleton H₁ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex₁]
  have h_met₂ : discreteModifiedMetric H₂ X = sInf {n | ∃ S : Finset (Cube d L), skeleton H₂ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex₂]
  rw [h_met₁, h_met₂]
  have h_ne : {n | ∃ S : Finset (Cube d L), skeleton H₁ X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n}.Nonempty :=
    ⟨X.card - 1, X, skeleton_subset H₁ X, by rfl, hconn, rfl⟩
  have h_mem := Nat.sInf_mem h_ne
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq] at h_mem ⊢
  rcases h_mem with ⟨S, hS_skel, hS_sub, hS_conn, h_eq⟩
  refine ⟨S, ?_, hS_sub, hS_conn, h_eq⟩
  exact h_mono.trans hS_skel

/-- For a connected polymer X with r in its skeleton, there exists a minimal connected
    spanning set S containing r and the skeleton, whose size is exactly the modified metric plus 1. -/
lemma exists_minimal_spanning_set {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L)) (r : Cube d L)
    (hr : r ∈ skeleton H X) (hconn : cubeConnected X) :
    ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ r ∈ S ∧ S.card = discreteModifiedMetric H X + 1 := by
  classical
  have h_ex : ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S :=
    ⟨X, skeleton_subset H X, by rfl, hconn⟩
  have h_metric : discreteModifiedMetric H X = sInf {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex]
  have h_ne : {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n}.Nonempty :=
    ⟨X.card - 1, X, skeleton_subset H X, by rfl, hconn, rfl⟩
  have h_mem := Nat.sInf_mem h_ne
  rw [← h_metric] at h_mem
  rcases h_mem with ⟨S, hS_skel, hS_sub, hS_conn, h_eq⟩
  have hrS : r ∈ S := hS_skel hr
  have hS_card : S.card ≥ 1 := Finset.card_pos.mpr ⟨r, hrS⟩
  refine ⟨S, hS_skel, hS_sub, hS_conn, hrS, ?_⟩
  omega


/-- **Skeleton-Fillings Multiplicity Bound** (Dimock Appendix E, preliminary combinatorial estimate for Lemma E.3).
    The polymer sum over all connected skeletons Y containing a fixed root r,
    weighted by the filling multiplicity and the exponential metric decay,
    is summable and bounded by a volume-independent constant.
    This is a preliminary combinatorial estimate, not the modified-metric summability itself. -/
theorem skeleton_fillings_weight_summable {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (r : Cube d L) (q : ℝ)
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d)) < 1) :
    ∑' Y : {S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w},
        ((admissibleFillings (cubeAdj d L) (Y : Finset (Cube d L)) H.holes).card : ℝ) * q ^ (Y : Finset (Cube d L)).card
      ≤ (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d)))⁻¹ := by
  classical
  let q' := q * 2 ^ (3 ^ d)
  have hq'0 : 0 ≤ q' := by
    dsimp [q']
    positivity
  have h_sum_le := cube_polymer_summable d L r hq'0 hCq
  have h_term_le : ∀ Y : {S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w},
      ((admissibleFillings (cubeAdj d L) (Y : Finset (Cube d L)) H.holes).card : ℝ) * q ^ (Y : Finset (Cube d L)).card ≤
      q' ^ (Y : Finset (Cube d L)).card := by
    intro Y
    let S := (Y : Finset (Cube d L))
    have hS_ne : S.Nonempty := ⟨r, Y.2.1⟩
    have h_card := cube_fillings_card_le_two_pow d L S H hdisj hnoedges hS_ne hholes_ne
    have h_two_pow : (2 ^ (3 ^ d * S.card) : ℝ) = (2 ^ (3 ^ d)) ^ S.card := by
      rw [pow_mul]
    have h_card_real : ((admissibleFillings (cubeAdj d L) S H.holes).card : ℝ) ≤ (2 ^ (3 ^ d)) ^ S.card := by
      rw [← h_two_pow]
      exact_mod_cast h_card
    have h_term_mul : ((admissibleFillings (cubeAdj d L) S H.holes).card : ℝ) * q ^ S.card ≤ ((2 ^ (3 ^ d)) ^ S.card) * q ^ S.card := by
      gcongr
    have h_pow_mul : ((2 ^ (3 ^ d)) ^ S.card) * q ^ S.card = q' ^ S.card := by
      dsimp [q']
      rw [mul_pow, mul_comm]
    exact h_term_mul.trans (h_pow_mul.symm ▸ le_refl _)
  have hf_summable : Summable (fun Y : {S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w} =>
      ((admissibleFillings (cubeAdj d L) (Y : Finset (Cube d L)) H.holes).card : ℝ) * q ^ (Y : Finset (Cube d L)).card) :=
    Summable.of_finite
  have hg_summable : Summable (fun Y : {S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w} =>
      q' ^ (Y : Finset (Cube d L)).card) :=
    Summable.of_finite
  have h_tsum := Summable.tsum_le_tsum h_term_le hf_summable hg_summable
  exact h_tsum.trans h_sum_le

/-- **Discrete Modified-Metric Summability** (Dimock Appendix E, Lemma E.3).
    The polymer sum over all connected, hole-respecting polymers X containing a fixed root r in their skeleton,
    weighted by the exponential metric decay q^(d_M(X) + 1), converges and is bounded by a volume-independent constant
    under the coordination entropy-suppression condition. -/
theorem discreteModifiedMetric_weight_summable {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (r : Cube d L) (q : ℝ)
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)) < 1) :
    ∑' X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
        q ^ (discreteModifiedMetric H (X : Finset (Cube d L)) + 1)
      ≤ (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹ := by
  classical
  let q' := q * 2 ^ (3 ^ d + 1)
  have hq'0 : 0 ≤ q' := by
    dsimp [q']
    positivity
  have h_sum_le := cube_polymer_summable d L r hq'0 hCq
  have h_S : ∀ X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
      ∃ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
        skeleton H X.1 ⊆ S.1 ∧ S.1 ⊆ X.1 ∧ S.1.card = discreteModifiedMetric H X.1 + 1 := by
    intro X
    obtain ⟨S, hS_skel, hS_sub, hS_conn, hrS, hS_card⟩ := exists_minimal_spanning_set H X.1 r X.2.1 X.2.2.1
    refine ⟨⟨S, hrS, ?_⟩, hS_skel, hS_sub, hS_card⟩
    intro x hx
    obtain ⟨w, hw⟩ := hS_conn r hrS x hx
    exact ⟨w, hw⟩
  let S_fn := fun X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X } =>
    Classical.choose (h_S X)
  have S_spec : ∀ X, skeleton H X.1 ⊆ (S_fn X).1 ∧ (S_fn X).1 ⊆ X.1 ∧ (S_fn X).1.card = discreteModifiedMetric H X.1 + 1 := by
    intro X
    exact Classical.choose_spec (h_S X)
  have h_tsum_eq : ∑' X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
      q ^ (discreteModifiedMetric H X.1 + 1) =
      ∑ X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
        q ^ (discreteModifiedMetric H X.1 + 1) := by
    rw [tsum_fintype]
  have h_fiber : ∑ X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
      q ^ (discreteModifiedMetric H X.1 + 1) =
      ∑ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
        ∑ X ∈ Finset.filter (fun X => S_fn X = S) Finset.univ,
          q ^ (discreteModifiedMetric H X.1 + 1) := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun X _ => Finset.mem_univ (S_fn X))]
  have h_inner_eq : ∀ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
      ∑ X ∈ Finset.filter (fun X => S_fn X = S) Finset.univ, q ^ (discreteModifiedMetric H X.1 + 1) =
      ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) * q ^ S.1.card := by
    intro S
    have h_const : ∀ X ∈ Finset.filter (fun X => S_fn X = S) Finset.univ, q ^ (discreteModifiedMetric H X.1 + 1) = q ^ S.1.card := by
      intro X hX
      rw [mem_filter] at hX
      have hS_eq : S_fn X = S := hX.2
      have hS_card := (S_spec X).2.2
      rw [hS_eq] at hS_card
      rw [hS_card]
    rw [Finset.sum_congr rfl h_const, Finset.sum_const, nsmul_eq_mul]
  have h_card_le : ∀ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
      ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) ≤ 2 ^ ((3 ^ d + 1) * S.1.card) := by
    intro S
    let Y_set := (powerset S.1).filter (fun Y => r ∈ Y)
    have h_subset : (Finset.filter (fun X => S_fn X = S) Finset.univ).map ⟨fun X => X.1, Subtype.val_injective⟩ ⊆
        Y_set.biUnion (fun Y => admissibleFillings (cubeAdj d L) Y H.holes) := by
      intro X hX
      rw [mem_map] at hX
      rcases hX with ⟨X_orig, hX_orig, rfl⟩
      rw [mem_filter] at hX_orig
      have hS_eq : S_fn X_orig = S := hX_orig.2
      have h_spec := S_spec X_orig
      rw [hS_eq] at h_spec
      rw [mem_biUnion]
      refine ⟨skeleton H X_orig.1, ?_, ?_⟩
      · rw [mem_filter, mem_powerset]
        refine ⟨h_spec.1, X_orig.2.1⟩
      · rw [admissibleFillings, mem_filter]
        refine ⟨mem_univ _, X_orig.2.2.1, X_orig.2.2.2, rfl⟩
    have h_card_map : (Finset.filter (fun X => S_fn X = S) Finset.univ).card =
        ((Finset.filter (fun X => S_fn X = S) Finset.univ).map ⟨fun X => X.1, Subtype.val_injective⟩).card := by
      rw [card_map]
    have h_biunion_card : (Y_set.biUnion (fun Y => admissibleFillings (cubeAdj d L) Y H.holes)).card ≤
        ∑ Y ∈ Y_set, (admissibleFillings (cubeAdj d L) Y H.holes).card :=
      card_biUnion_le
    have h_sum_fillings_le : ∑ Y ∈ Y_set, (admissibleFillings (cubeAdj d L) Y H.holes).card ≤
        ∑ Y ∈ Y_set, 2 ^ (3 ^ d * S.1.card) := by
      apply Finset.sum_le_sum
      intro Y hY
      rw [mem_filter, mem_powerset] at hY
      have hYne : Y.Nonempty := ⟨r, hY.2⟩
      have h_fillings := cube_fillings_card_le_two_pow d L Y H hdisj hnoedges hYne hholes_ne
      have h_card_mono : Y.card ≤ S.1.card := card_le_card hY.1
      have h_pow_mono : 3 ^ d * Y.card ≤ 3 ^ d * S.1.card := by
        gcongr
      have h_two_pow : 2 ^ (3 ^ d * Y.card) ≤ 2 ^ (3 ^ d * S.1.card) :=
        Nat.pow_le_pow_right (by decide) h_pow_mono
      exact h_fillings.trans h_two_pow
    have h_sum_const : ∑ Y ∈ Y_set, 2 ^ (3 ^ d * S.1.card) = Y_set.card * 2 ^ (3 ^ d * S.1.card) :=
      sum_const _
    have h_Y_set_card : Y_set.card ≤ 2 ^ S.1.card := by
      dsimp [Y_set]
      have : (powerset S.1).filter (fun Y => r ∈ Y) ⊆ powerset S.1 := filter_subset _ _
      have h_card := card_le_card this
      rw [card_powerset] at h_card
      exact h_card
    have h_total_le : Y_set.card * 2 ^ (3 ^ d * S.1.card) ≤ 2 ^ S.1.card * 2 ^ (3 ^ d * S.1.card) := by
      gcongr
    have h_exponents : 2 ^ S.1.card * 2 ^ (3 ^ d * S.1.card) = 2 ^ ((3 ^ d + 1) * S.1.card) := by
      rw [← pow_add]
      congr 1
      ring
    have h_card_le_nat : (Finset.filter (fun X => S_fn X = S) Finset.univ).card ≤ 2 ^ ((3 ^ d + 1) * S.1.card) := by
      have h1 : (Finset.filter (fun X => S_fn X = S) Finset.univ).card ≤ (Y_set.biUnion (fun Y => admissibleFillings (cubeAdj d L) Y H.holes)).card := by
        rw [h_card_map]
        exact card_le_card h_subset
      exact h1.trans (h_biunion_card.trans (h_sum_fillings_le.trans (h_sum_const ▸ h_total_le.trans_eq h_exponents)))
    exact_mod_cast h_card_le_nat
  have h_final_term_le : ∀ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
      ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) * q ^ S.1.card ≤ q' ^ S.1.card := by
    intro S
    have h_le := h_card_le S
    have h_pos_q : 0 ≤ q ^ S.1.card := by positivity
    have h_mul := mul_le_mul_of_nonneg_right h_le h_pos_q
    have h_geom : (2 ^ ((3 ^ d + 1) * S.1.card) : ℝ) * q ^ S.1.card = q' ^ S.1.card := by
      dsimp [q']
      rw [pow_mul, ← mul_pow, mul_comm]
    exact h_mul.trans (h_geom ▸ le_refl _)
  have h_sum_fiber_le : ∑ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
      ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) * q ^ S.1.card ≤
      (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹ := by
    have hf_summable : Summable (fun S => ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) * q ^ S.1.card) :=
      Summable.of_finite
    have hg_summable : Summable (fun S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w } => q' ^ S.1.card) :=
      Summable.of_finite
    have h_tsum := Summable.tsum_le_tsum h_final_term_le hf_summable hg_summable
    have h_tsum_eq_sum : ∑ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
        ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) * q ^ S.1.card =
        ∑' S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
          ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) * q ^ S.1.card := by
      rw [tsum_fintype]
    rw [h_tsum_eq_sum]
    exact h_tsum.trans h_sum_le
  rw [h_tsum_eq, h_fiber]
  have h_congr : ∑ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
      ∑ X ∈ Finset.filter (fun X => S_fn X = S) Finset.univ, q ^ (discreteModifiedMetric H X.1 + 1) =
      ∑ S : { S : Finset (Cube d L) // r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w },
        ((Finset.filter (fun X => S_fn X = S) Finset.univ).card : ℝ) * q ^ S.1.card := by
    refine Finset.sum_congr rfl (fun S _ => h_inner_eq S)
  rw [h_congr]
  exact h_sum_fiber_le

theorem discreteModifiedMetric_singleton_skeleton {d L : ℕ} (H : HoleFamily d L)
    (X : Finset (Cube d L)) (_hconn : cubeConnected X) (s : Cube d L)
    (hskel : skeleton H X = {s}) :
    discreteModifiedMetric H X = 0 := by
  classical
  have h_ex : ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S := by
    refine ⟨{s}, by rw [hskel], ?_, ?_⟩
    · rw [← hskel]
      exact skeleton_subset H X
    · intro x hx y hy
      rw [mem_singleton] at hx hy
      subst hx hy
      exact ⟨Walk.nil, fun v hv => by simp [Walk.support] at hv; subst hv; simp⟩
  have h_metric : discreteModifiedMetric H X = sInf {n | ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S ∧ S.card - 1 = n} := by
    unfold discreteModifiedMetric
    rw [dif_pos h_ex]
  rw [h_metric]
  apply Nat.sInf_eq_zero.mpr
  left
  simp only [Set.mem_setOf_eq]
  refine ⟨{s}, by rw [hskel], ?_, ?_, by simp⟩
  · rw [← hskel]
    exact skeleton_subset H X
  · intro x hx y hy
    rw [mem_singleton] at hx hy
    subst hx hy
    exact ⟨Walk.nil, fun v hv => by simp [Walk.support] at hv; subst hv; simp⟩

theorem discreteModifiedMetric_weight_summable_zero {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (r : Cube d L) :
    ∑' X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
        (0 : ℝ) ^ (discreteModifiedMetric H (X : Finset (Cube d L)) + 1)
      ≤ 1 := by
  have h_zero : (fun X : { X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X } =>
      (0 : ℝ) ^ (discreteModifiedMetric H (X : Finset (Cube d L)) + 1)) = fun _ => 0 := by
    ext X
    rw [zero_pow (Nat.succ_ne_zero _)]
  rw [h_zero, tsum_zero]
  exact zero_le_one

theorem discreteModifiedMetric_d_zero (H : HoleFamily 0 L) (X : Finset (Cube 0 L)) :
    discreteModifiedMetric H X = 0 := by
  classical
  unfold discreteModifiedMetric
  by_cases h_ex : ∃ S : Finset (Cube 0 L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S
  · rw [dif_pos h_ex]
    apply Nat.sInf_eq_zero.mpr
    left
    simp only [Set.mem_setOf_eq]
    obtain ⟨S, hS_skel, hS_sub, hS_conn⟩ := h_ex
    have h_card_le : S.card ≤ 1 := by
      by_contra h_gt
      push_neg at h_gt
      obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp h_gt
      have : x = y := funext (fun i => nomatch i)
      exact hne this
    by_cases hS_empty : S.card = 0
    · refine ⟨S, hS_skel, hS_sub, hS_conn, by omega⟩
    · have hS_one : S.card = 1 := by omega
      refine ⟨S, hS_skel, hS_sub, hS_conn, by omega⟩
  · rw [dif_neg h_ex]

theorem discreteModifiedMetric_L_one {d : ℕ} (H : HoleFamily d 1) (X : Finset (Cube d 1)) :
    discreteModifiedMetric H X = 0 := by
  classical
  unfold discreteModifiedMetric
  by_cases h_ex : ∃ S : Finset (Cube d 1), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S
  · rw [dif_pos h_ex]
    apply Nat.sInf_eq_zero.mpr
    left
    simp only [Set.mem_setOf_eq]
    obtain ⟨S, hS_skel, hS_sub, hS_conn⟩ := h_ex
    have h_card_le : S.card ≤ 1 := by
      by_contra h_gt
      push_neg at h_gt
      obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp h_gt
      have h_eq : x = y := by
        funext i
        exact Subsingleton.elim (x i) (y i)
      exact hne h_eq
    by_cases hS_empty : S.card = 0
    · refine ⟨S, hS_skel, hS_sub, hS_conn, by omega⟩
    · have hS_one : S.card = 1 := by omega
      refine ⟨S, hS_skel, hS_sub, hS_conn, by omega⟩
  · rw [dif_neg h_ex]

theorem discreteModifiedMetric_empty_skeleton {d L : ℕ} (H : HoleFamily d L) (X : Finset (Cube d L))
    (hskel : skeleton H X = ∅) :
    discreteModifiedMetric H X = 0 := by
  classical
  unfold discreteModifiedMetric
  by_cases h_ex : ∃ S : Finset (Cube d L), skeleton H X ⊆ S ∧ S ⊆ X ∧ cubeConnected S
  · rw [dif_pos h_ex]
    apply Nat.sInf_eq_zero.mpr
    left
    simp only [Set.mem_setOf_eq]
    refine ⟨∅, by rw [hskel], Finset.empty_subset _, ?_, by simp⟩
    intro x hx y hy
    simp at hx
  · rw [dif_neg h_ex]

theorem discreteModifiedMetric_d_one_empty_holes {L : ℕ} (H : HoleFamily 1 L) (hH : H.holes = ∅)
    (X : Finset (Cube 1 L)) (hconn : cubeConnected X) :
    discreteModifiedMetric H X = X.card - 1 :=
  discreteModifiedMetric_empty_holes H hH X hconn

end YangMills.RG
