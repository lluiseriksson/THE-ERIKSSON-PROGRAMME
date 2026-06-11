/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.LatticePolymerSystem
import YangMills.KP.SharpShell

/-!
# Cluster geometry, step B3 — connecting clusters are large

Half B of `docs/CLUSTER-CORRELATION-PLAN.md`: the geometric input of
the correlation decay.  A cluster of the connected lattice gas whose
support meets two distant plaquettes must contain many plaquettes:

* `touchGraph` — the global plaquette-touching graph and its distance;
* `touchGraph_dist_lt_card_of_connected` (B3a) — within one connected
  polymer, touching-distance is bounded by the plaquette count;
* `exists_touching_of_not_disjoint` (B3b) — overlapping supports
  produce a touching pair (the crossing step between incompatible
  polymers).

The cluster-level bound (B3c: distance ≤ linear in total size along
incompatibility paths) composes these and feeds the size-tail bound
`connectedLattice_pinned_tail_volumeUniform` (Half A).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open KP

variable {d N : ℕ} [NeZero N]

/-- The **global plaquette-touching graph**. -/
def touchGraph (d N : ℕ) [NeZero N] :
    SimpleGraph (ConcretePlaquette d N) :=
  SimpleGraph.fromRel plaquetteTouches

open Classical in
/-- **B3a: within-polymer distances are bounded by the size** —
a connected polymer realizes touching-paths between its members. -/
lemma touchGraph_dist_lt_card_of_connected
    {c : Finset (ConcretePlaquette d N)} (hc : IsConnectedPolymer c)
    {p q : ConcretePlaquette d N} (hp : p ∈ c) (hq : q ∈ c) :
    (touchGraph d N).dist p q < c.card := by
  classical
  have hadj : ∀ {x y : ↥c},
      (SimpleGraph.fromRel
        (fun p q : ↥c => plaquetteTouches p.1 q.1)).Adj x y →
      (touchGraph d N).Adj x.1 y.1 := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    show (SimpleGraph.fromRel plaquetteTouches).Adj x.1 y.1
    rw [SimpleGraph.fromRel_adj]
    exact ⟨fun h => hxy.1 (Subtype.ext h), hxy.2⟩
  have hdist : (SimpleGraph.fromRel
      (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
        ⟨p, hp⟩ ⟨q, hq⟩ < Fintype.card ↥c :=
    connected_dist_lt_card hc _ _
  obtain ⟨w, hw⟩ :=
    (hc.preconnected ⟨p, hp⟩ ⟨q, hq⟩).exists_walk_length_eq_dist
  have h1 : (touchGraph d N).dist p q
      ≤ (w.map ⟨Subtype.val, hadj⟩).length :=
    SimpleGraph.dist_le _
  rw [SimpleGraph.Walk.length_map, hw] at h1
  calc (touchGraph d N).dist p q
      ≤ (SimpleGraph.fromRel
          (fun p q : ↥c => plaquetteTouches p.1 q.1)).dist
            ⟨p, hp⟩ ⟨q, hq⟩ := h1
    _ < Fintype.card ↥c := hdist
    _ = c.card := Fintype.card_coe c

open Classical in
/-- **B3b: the crossing** — overlapping edge supports produce a
touching pair of plaquettes. -/
lemma exists_touching_of_not_disjoint
    {c c' : Finset (ConcretePlaquette d N)}
    (h : ¬ Disjoint (c.biUnion plaquetteSupport)
      (c'.biUnion plaquetteSupport)) :
    ∃ p ∈ c, ∃ q ∈ c', plaquetteTouches p q := by
  obtain ⟨e, he, he'⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨p, hp, hep⟩ := Finset.mem_biUnion.mp he
  obtain ⟨q, hq, heq⟩ := Finset.mem_biUnion.mp he'
  exact ⟨p, hp, q, hq,
    fun hd => (Finset.disjoint_left.mp hd hep) heq⟩

end YangMills
