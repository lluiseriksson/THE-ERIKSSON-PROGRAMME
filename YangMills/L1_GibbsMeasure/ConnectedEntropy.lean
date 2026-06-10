/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.LatticePolymerSystem

/-!
# Entropy of connected polymers, step 1 — local geometry

Opening of the volume-uniformity campaign (`docs/DEPENDENCY-GRAPH.md`):
the lattice-animal entropy bound for `connectedLatticePolymerSystem`
ultimately rests on a **local degree bound** — each plaquette touches a
volume-independent number of others.  This file provides its foundations:

* `FinBox.shift_injective` — the lattice shift is injective (periodic
  boundary: adding `1 mod N` in one coordinate is a bijection);
* `mem_plaquetteSupport_iff` — explicit 4-case characterization of the
  positive edges in a plaquette's support.

Next slices: the through-edge counting (`≤ 4d` plaquettes contain a given
edge), the touching-degree bound (`≤ 16d`), and the branching-process
entropy estimate.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

/-- **The lattice shift is injective** in the site argument (it has the
two-sided inverse `shiftBack`). -/
lemma FinBox.shift_injective {d N : ℕ} [NeZero N] (i : Fin d)
    {x y : FinBox d N} (h : x.shift i = y.shift i) : x = y := by
  calc x = (x.shift i).shiftBack i := (FinBox.shiftBack_shift x i).symm
    _ = (y.shift i).shiftBack i := by rw [h]
    _ = y := FinBox.shiftBack_shift y i

/-- **Explicit support membership:** a positive edge lies in a plaquette's
support iff it is one of the four corner edges. -/
lemma mem_plaquetteSupport_iff {d N : ℕ} [NeZero N]
    (q : ConcretePlaquette d N) (e : PosEdge d N) :
    e ∈ plaquetteSupport q ↔
      e = (q.edges 0).pos ∨ e = (q.edges 1).pos ∨
      e = (q.edges 2).pos ∨ e = (q.edges 3).pos := by
  unfold plaquetteSupport
  simp [Finset.mem_insert, Finset.mem_singleton]

section DegreeBound

variable {d N : ℕ} [NeZero N]

/-- The four corner edges of a plaquette, positively oriented, in closed
form (definitional). -/
lemma plaquette_pos_edges (r : ConcretePlaquette d N) :
    (r.edges 0).pos = (⟨⟨r.site, r.dir1, true⟩, rfl⟩ : PosEdge d N) ∧
    (r.edges 1).pos = (⟨⟨r.site.shift r.dir1, r.dir2, true⟩, rfl⟩ : PosEdge d N) ∧
    (r.edges 2).pos = (⟨⟨r.site.shift r.dir2, r.dir1, true⟩, rfl⟩ : PosEdge d N) ∧
    (r.edges 3).pos = (⟨⟨r.site, r.dir2, true⟩, rfl⟩ : PosEdge d N) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Through-edge counting:** at most `4d` plaquettes contain a given
positive edge in their support.  (The edge can sit in any of the 4 corner
slots, and the remaining direction of the plaquette is then the only free
datum.)  This is the volume-independent local input to the lattice-animal
entropy bound. -/
theorem card_plaquettesThroughEdge_le (e : PosEdge d N) :
    ((Finset.univ : Finset (ConcretePlaquette d N)).filter
      (fun q => e ∈ plaquetteSupport q)).card ≤ 4 * d := by
  classical
  set A0 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => e = (q.edges 0).pos) with hA0
  set A1 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => e = (q.edges 1).pos) with hA1
  set A2 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => e = (q.edges 2).pos) with hA2
  set A3 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => e = (q.edges 3).pos) with hA3
  -- the filter splits along the four slots
  have hsub : (Finset.univ : Finset (ConcretePlaquette d N)).filter
      (fun q => e ∈ plaquetteSupport q) ⊆ A0 ∪ A1 ∪ A2 ∪ A3 := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hq2 := (mem_plaquetteSupport_iff q e).mp hq.2
    simp only [hA0, hA1, hA2, hA3, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  -- slot 0: e = (q.site, q.dir1) — site and dir1 determined, dir2 free
  have h0 : A0.card ≤ d := by
    have hinj : Set.InjOn (fun q : ConcretePlaquette d N => q.dir2) ↑A0 := by
      intro q hq q' hq' hd
      simp only [hA0, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hq hq'
      have he : ((q.edges 0).pos : PosEdge d N) = (q'.edges 0).pos :=
        hq.symm.trans hq'
      rw [(plaquette_pos_edges q).1, (plaquette_pos_edges q').1] at he
      simp only [Subtype.mk.injEq, ConcreteEdge.mk.injEq, and_true] at he
      have hsite := he.1
      have hd1 := he.2
      cases q; cases q'
      simp_all
    calc A0.card ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ _) hinj
      _ = d := Finset.card_fin d
  -- slot 1: e = (q.site.shift q.dir1, q.dir2) — dir1 free
  have h1 : A1.card ≤ d := by
    have hinj : Set.InjOn (fun q : ConcretePlaquette d N => q.dir1) ↑A1 := by
      intro q hq q' hq' hd
      simp only [hA1, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hq hq'
      have he : ((q.edges 1).pos : PosEdge d N) = (q'.edges 1).pos :=
        hq.symm.trans hq'
      rw [(plaquette_pos_edges q).2.1, (plaquette_pos_edges q').2.1] at he
      simp only [Subtype.mk.injEq, ConcreteEdge.mk.injEq, and_true] at he
      have hd2 := he.2
      have he1 := he.1
      have hd' : q.dir1 = q'.dir1 := hd
      rw [hd'] at he1
      have hsite := FinBox.shift_injective q'.dir1 he1
      cases q; cases q'
      simp_all
    calc A1.card ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ _) hinj
      _ = d := Finset.card_fin d
  -- slot 2: e = (q.site.shift q.dir2, q.dir1) — dir2 free
  have h2 : A2.card ≤ d := by
    have hinj : Set.InjOn (fun q : ConcretePlaquette d N => q.dir2) ↑A2 := by
      intro q hq q' hq' hd
      simp only [hA2, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hq hq'
      have he : ((q.edges 2).pos : PosEdge d N) = (q'.edges 2).pos :=
        hq.symm.trans hq'
      rw [(plaquette_pos_edges q).2.2.1, (plaquette_pos_edges q').2.2.1] at he
      simp only [Subtype.mk.injEq, ConcreteEdge.mk.injEq, and_true] at he
      have hd1 := he.2
      have he1 := he.1
      have hd' : q.dir2 = q'.dir2 := hd
      rw [hd'] at he1
      have hsite := FinBox.shift_injective q'.dir2 he1
      cases q; cases q'
      simp_all
    calc A2.card ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ _) hinj
      _ = d := Finset.card_fin d
  -- slot 3: e = (q.site, q.dir2) — dir1 free
  have h3 : A3.card ≤ d := by
    have hinj : Set.InjOn (fun q : ConcretePlaquette d N => q.dir1) ↑A3 := by
      intro q hq q' hq' hd
      simp only [hA3, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hq hq'
      have he : ((q.edges 3).pos : PosEdge d N) = (q'.edges 3).pos :=
        hq.symm.trans hq'
      rw [(plaquette_pos_edges q).2.2.2, (plaquette_pos_edges q').2.2.2] at he
      simp only [Subtype.mk.injEq, ConcreteEdge.mk.injEq, and_true] at he
      have hsite := he.1
      have hd2 := he.2
      cases q; cases q'
      simp_all
    calc A3.card ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ _) hinj
      _ = d := Finset.card_fin d
  have hcard := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (A0 ∪ A1 ∪ A2) A3
  have hu2 := Finset.card_union_le (A0 ∪ A1) A2
  have hu3 := Finset.card_union_le A0 A1
  omega

instance plaquetteTouches.decidable {d N : ℕ} [NeZero N]
    (p q : ConcretePlaquette d N) : Decidable (plaquetteTouches p q) :=
  decidable_of_iff (¬ (plaquetteSupport p ∩ plaquetteSupport q = ∅)) (by
    unfold plaquetteTouches
    exact not_congr Finset.disjoint_iff_inter_eq_empty.symm)

/-- **THE LOCAL DEGREE BOUND:** each plaquette touches at most `16d` others
(including itself) — a volume-independent constant.  This is the seed of
every lattice-animal entropy estimate: connected polymers grow inside a
bounded-degree graph. -/
theorem card_plaquettesTouching_le (p : ConcretePlaquette d N) :
    ((Finset.univ : Finset (ConcretePlaquette d N)).filter
      (fun q => plaquetteTouches p q)).card ≤ 16 * d := by
  classical
  set B0 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => (p.edges 0).pos ∈ plaquetteSupport q) with hB0
  set B1 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => (p.edges 1).pos ∈ plaquetteSupport q) with hB1
  set B2 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => (p.edges 2).pos ∈ plaquetteSupport q) with hB2
  set B3 := (Finset.univ : Finset (ConcretePlaquette d N)).filter
    (fun q => (p.edges 3).pos ∈ plaquetteSupport q) with hB3
  have hsub : (Finset.univ : Finset (ConcretePlaquette d N)).filter
      (fun q => plaquetteTouches p q) ⊆ B0 ∪ B1 ∪ B2 ∪ B3 := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨x, hxp, hxq⟩ := Finset.not_disjoint_iff.mp hq.2
    have hx := (mem_plaquetteSupport_iff p x).mp hxp
    simp only [hB0, hB1, hB2, hB3, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rcases hx with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (h ▸ hxq)))
    · exact Or.inl (Or.inl (Or.inr (h ▸ hxq)))
    · exact Or.inl (Or.inr (h ▸ hxq))
    · exact Or.inr (h ▸ hxq)
  have hcard := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (B0 ∪ B1 ∪ B2) B3
  have hu2 := Finset.card_union_le (B0 ∪ B1) B2
  have hu3 := Finset.card_union_le B0 B1
  have hb0 : B0.card ≤ 4 * d := card_plaquettesThroughEdge_le _
  have hb1 : B1.card ≤ 4 * d := card_plaquettesThroughEdge_le _
  have hb2 : B2.card ≤ 4 * d := card_plaquettesThroughEdge_le _
  have hb3 : B3.card ≤ 4 * d := card_plaquettesThroughEdge_le _
  omega

end DegreeBound

section WalkCounting

/-- **The walk-counting engine:** in a relation of out-degree at most `Δ`
on a finite type, there are at most `Δ^L` walks of length `L` from a fixed
start (walks as functions `Fin (L+1) → V`).  Proof: chop off the last step;
each fiber of the restriction map injects into the out-neighbourhood of the
walk's penultimate vertex.  Combined with the degree bound `≤ 16d` and the
(forthcoming) spanning-walk encoding of connected sets, this yields the
volume-uniform lattice-animal entropy bound. -/
theorem card_relWalks_le {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] (Δ : ℕ)
    (hdeg : ∀ v, ((Finset.univ : Finset V).filter (fun w => R v w)).card ≤ Δ)
    (v₀ : V) (L : ℕ) :
    ((Finset.univ : Finset (Fin (L + 1) → V)).filter
      (fun w => w 0 = v₀ ∧ ∀ k : Fin L, R (w k.castSucc) (w k.succ))).card
      ≤ Δ ^ L := by
  induction L with
  | zero =>
      rw [pow_zero]
      refine Finset.card_le_one.mpr ?_
      intro w hw w' hw'
      rw [Finset.mem_filter] at hw hw'
      funext k
      have hk : k = 0 := by omega
      rw [hk, hw.2.1, hw'.2.1]
  | succ n ih =>
      set s := ((Finset.univ : Finset (Fin (n + 2) → V)).filter
        (fun w => w 0 = v₀ ∧
          ∀ k : Fin (n + 1), R (w k.castSucc) (w k.succ))) with hs
      set f : (Fin (n + 2) → V) → (Fin (n + 1) → V) :=
        (fun w => w ∘ Fin.castSucc) with hf
      -- the image of the restriction map consists of walks of length n
      have himage : s.image f ⊆
          ((Finset.univ : Finset (Fin (n + 1) → V)).filter
            (fun w => w 0 = v₀ ∧
              ∀ k : Fin n, R (w k.castSucc) (w k.succ))) := by
        intro y hy
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        rw [hs, Finset.mem_filter] at hw
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · show w (Fin.castSucc 0) = v₀
          rw [show (Fin.castSucc 0 : Fin (n + 2)) = 0 from rfl]
          exact hw.2.1
        · intro k
          have := hw.2.2 k.castSucc
          show R (w k.castSucc.castSucc) (w k.succ.castSucc)
          rwa [← Fin.succ_castSucc]
      -- each fiber injects into an out-neighbourhood
      have hfiber : ∀ y ∈ s.image f,
          (s.filter (fun w => f w = y)).card ≤ Δ := by
        intro y _
        have hmaps : ∀ w ∈ s.filter (fun w => f w = y),
            w (Fin.last (n + 1)) ∈
              (Finset.univ : Finset V).filter
                (fun v => R (y (Fin.last n)) v) := by
          intro w hw
          rw [Finset.mem_filter] at hw
          obtain ⟨hws, hwf⟩ := hw
          rw [hs, Finset.mem_filter] at hws
          have hstep := hws.2.2 (Fin.last n)
          rw [Fin.succ_last] at hstep
          have hpen : w (Fin.last n).castSucc = y (Fin.last n) := by
            rw [← hwf]
            rfl
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hpen ▸ hstep⟩
        have hinj : Set.InjOn (fun w : Fin (n + 2) → V => w (Fin.last (n + 1)))
            ↑(s.filter (fun w => f w = y)) := by
          intro w hw w' hw' hlast
          rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
          funext k
          refine Fin.lastCases ?_ ?_ k
          · exact hlast
          · intro j
            have h1 : f w j = f w' j := by rw [hw.2, hw'.2]
            exact h1
        calc (s.filter (fun w => f w = y)).card
            ≤ ((Finset.univ : Finset V).filter
                (fun v => R (y (Fin.last n)) v)).card :=
              Finset.card_le_card_of_injOn _ hmaps hinj
          _ ≤ Δ := hdeg _
      calc s.card ≤ Δ * (s.image f).card :=
            Finset.card_le_mul_card_image s Δ hfiber
        _ ≤ Δ * Δ ^ n :=
            Nat.mul_le_mul_left Δ (le_trans (Finset.card_le_card himage) ih)
        _ = Δ ^ (n + 1) := by ring

end WalkCounting

section LazyWalks

variable {V : Type*}

/-- A **lazy closed walk**: starts and ends at `v₀`, and every step either
moves along the relation or stays put.  Laziness lets walks have any fixed
even length without padding gymnastics; the cost is one extra unit of
out-degree in the counting, absorbed into the entropy constant. -/
def IsLazyClosedWalk (R : V → V → Prop) (v₀ : V) {L : ℕ}
    (w : Fin (L + 1) → V) : Prop :=
  w 0 = v₀ ∧ w (Fin.last L) = v₀ ∧
    ∀ k : Fin L, R (w k.castSucc) (w k.succ) ∨ w k.castSucc = w k.succ

/-- Laziness costs one unit of out-degree. -/
lemma card_lazy_neighbors_le [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] (Δ : ℕ)
    (hdeg : ∀ v, ((Finset.univ : Finset V).filter (fun u => R v u)).card ≤ Δ)
    (v : V) :
    ((Finset.univ : Finset V).filter (fun u => R v u ∨ v = u)).card ≤ Δ + 1 := by
  classical
  have hsub : (Finset.univ : Finset V).filter (fun u => R v u ∨ v = u)
      ⊆ ((Finset.univ : Finset V).filter (fun u => R v u)) ∪ {v} := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hu.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu.1, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h.symm)
  calc ((Finset.univ : Finset V).filter (fun u => R v u ∨ v = u)).card
      ≤ (((Finset.univ : Finset V).filter (fun u => R v u)) ∪ {v}).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset V).filter (fun u => R v u)).card + ({v} : Finset V).card :=
        Finset.card_union_le _ _
    _ ≤ Δ + 1 := by
        have := hdeg v
        simp only [Finset.card_singleton]
        omega

/-- **The splice lemma:** a lazy closed walk can be extended by two steps to
additionally visit any vertex adjacent to a vertex it already visits.  This
is the inductive engine of the spanning-walk encoding of connected sets. -/
lemma IsLazyClosedWalk.extend [DecidableEq V] {R : V → V → Prop}
    (hsym : ∀ a b, R a b → R b a) {v₀ : V} {L : ℕ} {w : Fin (L + 1) → V}
    (hw : IsLazyClosedWalk R v₀ w) (k : Fin (L + 1)) {x : V}
    (hx : R (w k) x) :
    ∃ w' : Fin (L + 3) → V, IsLazyClosedWalk R v₀ w' ∧
      Finset.image w' Finset.univ = insert x (Finset.image w Finset.univ) := by
  obtain ⟨hw0, hwlast, hwstep⟩ := hw
  refine ⟨fun i => if h : (i : ℕ) ≤ (k : ℕ) then w ⟨i, by omega⟩
    else if (i : ℕ) = (k : ℕ) + 1 then x
    else w ⟨(i : ℕ) - 2, by omega⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- starts at v₀
    dsimp only
    have h0 : ((0 : Fin (L + 3)) : ℕ) ≤ (k : ℕ) := Nat.zero_le _
    rw [dif_pos h0]
    have : (⟨((0 : Fin (L + 3)) : ℕ), by omega⟩ : Fin (L + 1)) = 0 := rfl
    rw [this, hw0]
  · -- ends at v₀
    dsimp only
    have hkL : (k : ℕ) ≤ L := by omega
    have h1 : ¬ ((Fin.last (L + 2) : ℕ) ≤ (k : ℕ)) := by
      simp only [Fin.val_last]; omega
    have h2 : ¬ ((Fin.last (L + 2) : ℕ) = (k : ℕ) + 1) := by
      simp only [Fin.val_last]; omega
    rw [dif_neg h1, if_neg h2]
    have : (⟨(Fin.last (L + 2) : ℕ) - 2, by omega⟩ : Fin (L + 1)) = Fin.last L := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [this, hwlast]
  · -- steps
    intro j
    dsimp only
    have hjcast : ((j.castSucc : Fin (L + 3)) : ℕ) = (j : ℕ) := rfl
    have hjsucc : ((j.succ : Fin (L + 3)) : ℕ) = (j : ℕ) + 1 := rfl
    by_cases hc1 : (j : ℕ) + 1 ≤ (k : ℕ)
    · -- entirely inside the prefix
      rw [dif_pos (by omega : ((j.castSucc : Fin (L + 3)) : ℕ) ≤ (k : ℕ)),
        dif_pos (by rw [hjsucc]; omega)]
      have hjL : (j : ℕ) < L := by omega
      have hcs : (⟨((j.castSucc : Fin (L + 3)) : ℕ), by omega⟩ : Fin (L + 1))
          = (⟨(j : ℕ), hjL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [hjcast]
      have hsc : (⟨((j.succ : Fin (L + 3)) : ℕ), by omega⟩ : Fin (L + 1))
          = (⟨(j : ℕ), hjL⟩ : Fin L).succ := by
        apply Fin.ext; simp [hjsucc]
      rw [hcs, hsc]
      exact hwstep _
    · by_cases hc2 : (j : ℕ) = (k : ℕ)
      · -- the step into x
        rw [dif_pos (by omega : ((j.castSucc : Fin (L + 3)) : ℕ) ≤ (k : ℕ)),
          dif_neg (by rw [hjsucc]; omega), if_pos (by rw [hjsucc]; omega)]
        have : (⟨((j.castSucc : Fin (L + 3)) : ℕ), by omega⟩ : Fin (L + 1)) = k := by
          apply Fin.ext; simp [hjcast, hc2]
        rw [this]
        exact Or.inl hx
      · by_cases hc3 : (j : ℕ) = (k : ℕ) + 1
        · -- the step back from x
          rw [dif_neg (by rw [hjcast]; omega), if_pos (by rw [hjcast]; omega),
            dif_neg (by rw [hjsucc]; omega), if_neg (by rw [hjsucc]; omega)]
          have : (⟨((j.succ : Fin (L + 3)) : ℕ) - 2, by omega⟩ : Fin (L + 1)) = k := by
            apply Fin.ext
            simp only [hjsucc]
            omega
          rw [this]
          exact Or.inl (hsym _ _ hx)
        · -- entirely inside the shifted suffix
          have hge : (k : ℕ) + 2 ≤ (j : ℕ) := by omega
          rw [dif_neg (by rw [hjcast]; omega), if_neg (by rw [hjcast]; omega),
            dif_neg (by rw [hjsucc]; omega), if_neg (by rw [hjsucc]; omega)]
          have hjL : (j : ℕ) - 2 < L := by omega
          have hcs : (⟨((j.castSucc : Fin (L + 3)) : ℕ) - 2, by omega⟩ : Fin (L + 1))
              = (⟨(j : ℕ) - 2, hjL⟩ : Fin L).castSucc := by
            apply Fin.ext; simp [hjcast]
          have hsc : (⟨((j.succ : Fin (L + 3)) : ℕ) - 2, by omega⟩ : Fin (L + 1))
              = (⟨(j : ℕ) - 2, hjL⟩ : Fin L).succ := by
            apply Fin.ext
            simp only [hjsucc, Fin.succ_mk]
            omega
          rw [hcs, hsc]
          exact hwstep _
  · -- the range gains exactly x
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases h1 : (i : ℕ) ≤ (k : ℕ)
      · rw [dif_pos h1]
        exact Or.inr ⟨_, rfl⟩
      · by_cases h2 : (i : ℕ) = (k : ℕ) + 1
        · rw [dif_neg h1, if_pos h2]
          exact Or.inl rfl
        · rw [dif_neg h1, if_neg h2]
          exact Or.inr ⟨_, rfl⟩
    · rintro (rfl | ⟨j, rfl⟩)
      · -- x is hit at index k+1
        refine ⟨⟨(k : ℕ) + 1, by omega⟩, ?_⟩
        rw [dif_neg (by simp), if_pos (by simp)]
      · by_cases h1 : (j : ℕ) ≤ (k : ℕ)
        · refine ⟨⟨(j : ℕ), by omega⟩, ?_⟩
          rw [dif_pos (by simpa using h1)]
        · refine ⟨⟨(j : ℕ) + 2, by omega⟩, ?_⟩
          rw [dif_neg (by simp; omega), if_neg (by simp; omega)]
          congr 1

/-- **First-exit crossing:** a graph walk from inside `S` to outside `S`
uses an edge from `S` to its complement. -/
lemma exists_adj_crossing_of_walk {α : Type*} {G : SimpleGraph α} {S : Set α} :
    ∀ {a b : α}, G.Walk a b → a ∈ S → b ∉ S →
      ∃ u v, G.Adj u v ∧ u ∈ S ∧ v ∉ S := by
  intro a b p
  induction p with
  | nil => intro ha hb; exact absurd ha hb
  | @cons u v w h q ih =>
      intro ha hb
      by_cases hv : v ∈ S
      · exact ih hv hb
      · exact ⟨u, v, h, ha, hv⟩

private lemma covering_aux {V : Type*} [DecidableEq V] {R : V → V → Prop}
    (hsym : ∀ a b, R a b → R b a) {c : Finset V} {v₀ : V}
    (hcross : ∀ s : Finset V, v₀ ∈ s → s ⊆ c → s ≠ c →
      ∃ y ∈ s, ∃ x ∈ c, x ∉ s ∧ R y x) :
    ∀ (m : ℕ) (s : Finset V), v₀ ∈ s → s ⊆ c → c.card - s.card = m →
      ∀ (L : ℕ) (w : Fin (L + 1) → V), IsLazyClosedWalk R v₀ w →
        Finset.image w Finset.univ = s →
        ∃ (L' : ℕ) (w' : Fin (L' + 1) → V), L' = L + 2 * m ∧
          IsLazyClosedWalk R v₀ w' ∧ Finset.image w' Finset.univ = c := by
  intro m
  induction m with
  | zero =>
      intro s hv hsub hcard L w hw himg
      have hle : c.card ≤ s.card := by
        have := Finset.card_le_card hsub
        omega
      have hsc : s = c := Finset.eq_of_subset_of_card_le hsub hle
      exact ⟨L, w, by omega, hw, hsc ▸ himg⟩
  | succ m ih =>
      intro s hv hsub hcard L w hw himg
      have hne : s ≠ c := by
        intro h
        rw [h] at hcard
        omega
      obtain ⟨y, hy, x, hxc, hxs, hxy⟩ := hcross s hv hsub hne
      have hyim : y ∈ Finset.image w Finset.univ := himg ▸ hy
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hyim
      have hRk : R (w k) x := by rw [hk]; exact hxy
      obtain ⟨w₂, hw₂, himg₂⟩ := hw.extend hsym k hRk
      have himg₂' : Finset.image w₂ Finset.univ = insert x s := by
        rw [himg₂, himg]
      obtain ⟨L', w', hL', hw', himgc⟩ := ih (insert x s)
        (Finset.mem_insert_of_mem hv)
        (Finset.insert_subset hxc hsub)
        (by rw [Finset.card_insert_of_notMem hxs]; omega)
        (L + 2) w₂ hw₂ himg₂'
      exact ⟨L', w', by omega, hw', himgc⟩

/-- **THE COVERING-WALK THEOREM:** any finite set with the boundary-crossing
property (in particular: any connected set) containing `v₀` is the exact
range of a lazy closed walk from `v₀` of length `2(|c| − 1)`.  Greedy
growth: while the walk's range is a proper subset, connectivity provides a
boundary edge and the splice lemma absorbs it.  With `card_relWalks_le`
this caps the number of such sets by `(Δ+1)^{2(|c|−1)}` — the
volume-independent lattice-animal entropy bound. -/
theorem exists_covering_lazyWalk {V : Type*} [DecidableEq V]
    (R : V → V → Prop) (hsym : ∀ a b, R a b → R b a)
    (c : Finset V) (v₀ : V) (hv₀ : v₀ ∈ c)
    (hcross : ∀ s : Finset V, v₀ ∈ s → s ⊆ c → s ≠ c →
      ∃ y ∈ s, ∃ x ∈ c, x ∉ s ∧ R y x) :
    ∃ w : Fin (2 * (c.card - 1) + 1) → V,
      IsLazyClosedWalk R v₀ w ∧ Finset.image w Finset.univ = c := by
  have hbase : IsLazyClosedWalk R v₀ (fun _ : Fin 1 => v₀) :=
    ⟨rfl, rfl, fun k => k.elim0⟩
  have hbimg : Finset.image (fun _ : Fin 1 => v₀) Finset.univ = {v₀} := by
    simp
  obtain ⟨L', w', hL', hw', himg⟩ := covering_aux hsym hcross (c.card - 1)
    {v₀} (Finset.mem_singleton_self v₀)
    (Finset.singleton_subset_iff.mpr hv₀)
    (by rw [Finset.card_singleton]) 0 (fun _ => v₀) hbase hbimg
  have hL : L' = 2 * (c.card - 1) := by omega
  subst hL
  exact ⟨w', hw', himg⟩

/-- Variant of the covering-walk theorem exposing the length as an
existential with an equation — convenient for consumers that know `c.card`
only propositionally. -/
theorem exists_covering_lazyWalk_len {V : Type*} [DecidableEq V]
    (R : V → V → Prop) (hsym : ∀ a b, R a b → R b a)
    (c : Finset V) (v₀ : V) (hv₀ : v₀ ∈ c)
    (hcross : ∀ s : Finset V, v₀ ∈ s → s ⊆ c → s ≠ c →
      ∃ y ∈ s, ∃ x ∈ c, x ∉ s ∧ R y x) :
    ∃ (L : ℕ) (w : Fin (L + 1) → V), L = 2 * (c.card - 1) ∧
      IsLazyClosedWalk R v₀ w ∧ Finset.image w Finset.univ = c := by
  have hbase : IsLazyClosedWalk R v₀ (fun _ : Fin 1 => v₀) :=
    ⟨rfl, rfl, fun k => k.elim0⟩
  have hbimg : Finset.image (fun _ : Fin 1 => v₀) Finset.univ = {v₀} := by
    simp
  obtain ⟨L', w', hL', hw', himg⟩ := covering_aux hsym hcross (c.card - 1)
    {v₀} (Finset.mem_singleton_self v₀)
    (Finset.singleton_subset_iff.mpr hv₀)
    (by rw [Finset.card_singleton]) 0 (fun _ => v₀) hbase hbimg
  exact ⟨L', w', by omega, hw', himg⟩

end LazyWalks

section ConnectedCrossing

variable {d N : ℕ} [NeZero N]

/-- The touching relation is symmetric. -/
lemma plaquetteTouches_symm {p q : ConcretePlaquette d N}
    (h : plaquetteTouches p q) : plaquetteTouches q p :=
  fun hd => h hd.symm

/-- **Connected polymers have the boundary-crossing property:** any proper
subset of a connected polymer containing a marked plaquette is joined to its
complement by a touching pair.  This is the `hcross` hypothesis of the
covering-walk theorem, discharged for `IsConnectedPolymer`. -/
lemma isConnectedPolymer_crossing
    {c : Finset (ConcretePlaquette d N)} (hc : IsConnectedPolymer c)
    {v₀ : ConcretePlaquette d N} (hv₀c : v₀ ∈ c) :
    ∀ s : Finset (ConcretePlaquette d N), v₀ ∈ s → s ⊆ c → s ≠ c →
      ∃ y ∈ s, ∃ x ∈ c, x ∉ s ∧ plaquetteTouches y x := by
  intro s hv₀s hsub hne
  have hss : s ⊂ c :=
    ⟨hsub, fun h => hne (Finset.Subset.antisymm hsub h)⟩
  obtain ⟨x₀, hx₀c, hx₀s⟩ := Finset.exists_of_ssubset hss
  have hconn := hc
  unfold IsConnectedPolymer at hconn
  obtain ⟨p⟩ := hconn.preconnected ⟨v₀, hv₀c⟩ ⟨x₀, hx₀c⟩
  obtain ⟨u, v, hadj, hu, hv⟩ := exists_adj_crossing_of_walk
    (S := {t : ↥c | t.1 ∈ s}) p hv₀s hx₀s
  rw [SimpleGraph.fromRel_adj] at hadj
  rcases hadj.2 with h | h
  · exact ⟨u.1, hu, v.1, v.2, hv, h⟩
  · exact ⟨u.1, hu, v.1, v.2, hv, plaquetteTouches_symm h⟩

open Classical in
/-- **THE LATTICE-ANIMAL ENTROPY BOUND (volume-uniform):** the number of
connected polymers of size `n+1` through a fixed plaquette is at most
`(16d+1)^{2n}` — a constant depending only on the dimension, **not on the
lattice volume**.  Proof: every such polymer is the exact range of a lazy
closed walk of length `2n` from `p₀` (covering-walk theorem + crossing
property), and there are at most `(16d+1)^{2n}` such walks (degree bound +
walk counting).  This is the entropy input that makes the KP criterion for
the connected gas volume-uniform. -/
theorem card_connectedPolymers_le {d N : ℕ} [NeZero N]
    (p₀ : ConcretePlaquette d N) (n : ℕ) :
    ((Finset.univ : Finset (Finset (ConcretePlaquette d N))).filter
      (fun c => p₀ ∈ c ∧ IsConnectedPolymer c ∧ c.card = n + 1)).card
      ≤ (16 * d + 1) ^ (2 * n) := by
  classical
  set Rlazy : ConcretePlaquette d N → ConcretePlaquette d N → Prop :=
    fun p q => plaquetteTouches p q ∨ p = q with hR
  have hdeg : ∀ v, ((Finset.univ : Finset (ConcretePlaquette d N)).filter
      (fun u => Rlazy v u)).card ≤ 16 * d + 1 := fun v =>
    card_lazy_neighbors_le plaquetteTouches (16 * d)
      card_plaquettesTouching_le v
  have hsurj : Set.SurjOn
      (fun w : Fin (2 * n + 1) → ConcretePlaquette d N =>
        Finset.image w Finset.univ)
      ↑((Finset.univ : Finset (Fin (2 * n + 1) → ConcretePlaquette d N)).filter
        (fun w => w 0 = p₀ ∧
          ∀ k : Fin (2 * n), Rlazy (w k.castSucc) (w k.succ)))
      ↑((Finset.univ : Finset (Finset (ConcretePlaquette d N))).filter
        (fun c => p₀ ∈ c ∧ IsConnectedPolymer c ∧ c.card = n + 1)) := by
    intro c hcmem
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hcmem
    obtain ⟨hp₀, hconn, hcard⟩ := hcmem
    obtain ⟨L, w, hL, hw, himg⟩ := exists_covering_lazyWalk_len
      plaquetteTouches (fun _ _ h => plaquetteTouches_symm h) c p₀ hp₀
      (isConnectedPolymer_crossing hconn hp₀)
    have hL' : L = 2 * n := by
      rw [hcard] at hL
      omega
    subst hL'
    refine ⟨w, ?_, himg⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact ⟨hw.1, fun k => hw.2.2 k⟩
  calc ((Finset.univ : Finset (Finset (ConcretePlaquette d N))).filter
        (fun c => p₀ ∈ c ∧ IsConnectedPolymer c ∧ c.card = n + 1)).card
      ≤ ((Finset.univ : Finset (Fin (2 * n + 1) → ConcretePlaquette d N)).filter
          (fun w => w 0 = p₀ ∧
            ∀ k : Fin (2 * n), Rlazy (w k.castSucc) (w k.succ))).card :=
        Finset.card_le_card_of_surjOn _ hsurj
    _ ≤ (16 * d + 1) ^ (2 * n) :=
        card_relWalks_le Rlazy (16 * d + 1) hdeg p₀ (2 * n)

open Classical in
/-- **Per-plaquette geometric cluster bound (volume-uniform):** the weighted
sum over all connected polymers through a fixed plaquette, with weight
`x^{size}`, is at most `x / (1 − (16d+1)²x)` whenever `(16d+1)²x < 1` —
independent of the lattice volume.  Fiberwise by size + the lattice-animal
entropy bound + a geometric series. -/
theorem sum_connectedPolymers_through_le {d N : ℕ} [NeZero N]
    (p : ConcretePlaquette d N) (x : ℝ) (hx : 0 ≤ x)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x < 1) :
    ∑ c' ∈ (Finset.univ : Finset {c : Finset (ConcretePlaquette d N) //
        c.Nonempty ∧ IsConnectedPolymer c}).filter (fun c' => p ∈ c'.1),
      x ^ c'.1.card ≤ x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x) := by
  classical
  set M := Fintype.card (ConcretePlaquette d N) with hM
  set r : ℝ := ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x with hrdef
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hden : (0 : ℝ) < 1 - r := by linarith
  set S := (Finset.univ : Finset {c : Finset (ConcretePlaquette d N) //
    c.Nonempty ∧ IsConnectedPolymer c}).filter (fun c' => p ∈ c'.1) with hS
  -- fiberwise decomposition by polymer size
  have hmaps : ∀ c' ∈ S, c'.1.card ∈ Finset.range (M + 1) := by
    intro c' _
    rw [Finset.mem_range]
    have := Finset.card_le_univ c'.1
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun c' => x ^ c'.1.card)
  rw [← hfib]
  -- each fiber is a constant times its cardinality
  have hfiber_eq : ∀ y ∈ Finset.range (M + 1),
      ∑ c' ∈ S.filter (fun c' => c'.1.card = y), x ^ c'.1.card
        = (S.filter (fun c' => c'.1.card = y)).card * x ^ y := by
    intro y _
    rw [Finset.sum_congr rfl (fun c' hc' => by
      rw [(Finset.mem_filter.mp hc').2]), Finset.sum_const, nsmul_eq_mul]
  -- the size-0 fiber is empty
  have hzero : S.filter (fun c' => c'.1.card = 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro c' _
    have := c'.2.1.card_pos
    omega
  -- fibers of size j+1 are bounded by the animal count
  have hcount : ∀ j : ℕ, ((S.filter (fun c' => c'.1.card = j + 1)).card : ℝ)
      ≤ ((16 * d + 1 : ℕ) : ℝ) ^ (2 * j) := by
    intro j
    have hinj : Set.InjOn (fun c' : {c : Finset (ConcretePlaquette d N) //
        c.Nonempty ∧ IsConnectedPolymer c} => c'.1)
        ↑(S.filter (fun c' => c'.1.card = j + 1)) :=
      fun a _ b _ h => Subtype.ext h
    have hmaps2 : ∀ c' ∈ S.filter (fun c' => c'.1.card = j + 1),
        c'.1 ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d N))).filter
          (fun c => p ∈ c ∧ IsConnectedPolymer c ∧ c.card = j + 1) := by
      intro c' hc'
      rw [Finset.mem_filter] at hc'
      obtain ⟨hcS, hcard⟩ := hc'
      rw [hS, Finset.mem_filter] at hcS
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcS.2, c'.2.2, hcard⟩
    have h1 : (S.filter (fun c' => c'.1.card = j + 1)).card
        ≤ ((Finset.univ : Finset (Finset (ConcretePlaquette d N))).filter
          (fun c => p ∈ c ∧ IsConnectedPolymer c ∧ c.card = j + 1)).card :=
      Finset.card_le_card_of_injOn _ hmaps2 hinj
    have h2 := card_connectedPolymers_le p j
    exact_mod_cast le_trans h1 h2
  -- assemble: shift the range and sum the geometric series
  calc ∑ y ∈ Finset.range (M + 1),
        ∑ c' ∈ S.filter (fun c' => c'.1.card = y), x ^ c'.1.card
      = ∑ y ∈ Finset.range (M + 1),
          ((S.filter (fun c' => c'.1.card = y)).card : ℝ) * x ^ y :=
        Finset.sum_congr rfl hfiber_eq
    _ = (∑ j ∈ Finset.range M,
          ((S.filter (fun c' => c'.1.card = j + 1)).card : ℝ) * x ^ (j + 1))
        + ((S.filter (fun c' => c'.1.card = 0)).card : ℝ) * x ^ 0 :=
        Finset.sum_range_succ' _ M
    _ = ∑ j ∈ Finset.range M,
          ((S.filter (fun c' => c'.1.card = j + 1)).card : ℝ) * x ^ (j + 1) := by
        rw [hzero]
        simp
    _ ≤ ∑ j ∈ Finset.range M,
          ((16 * d + 1 : ℕ) : ℝ) ^ (2 * j) * x ^ (j + 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right (hcount j) (by positivity)
    _ = x * ∑ j ∈ Finset.range M, r ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hrdef, mul_pow, pow_mul, pow_succ]
        ring
    _ ≤ x * (1 / (1 - r)) := by
        refine mul_le_mul_of_nonneg_left ?_ hx
        have hgeom : ∑ j ∈ Finset.range M, r ^ j = (1 - r ^ M) / (1 - r) := by
          rw [geom_sum_eq (by linarith : r ≠ 1)]
          rw [div_eq_div_iff (by linarith) (by linarith)]
          ring
        rw [hgeom, div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right
          (by linarith [pow_nonneg hr0 M]) (inv_nonneg.mpr hden.le)
    _ = x / (1 - r) := by
        rw [mul_one_div]

end ConnectedCrossing

section UniformCriterion

open MeasureTheory KP

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-- **THE VOLUME-UNIFORM KOTECKÝ–PREISS CRITERION** for the connected
lattice gas: under smallness conditions on `β` that depend **only on the
dimension `d`** (through the local geometry constants `16d` and `(16d+1)²`)
— never on the lattice volume — the KP criterion holds for
`connectedLatticePolymerSystem` with weight `a(c) = t·|c|`.

Every incompatible polymer is steered through a touching plaquette
(indicator domination), counted by the per-plaquette geometric cluster
bound, which rests on the lattice-animal entropy bound.  This discharges
the volume-uniformity caveat recorded for the earlier (binomial-entropy)
criterion. -/
theorem connectedLatticePolymerSystem_kpCriterion_volumeUniform
    (μ : Measure G) [IsProbabilityMeasure μ] {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp t) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp t) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp t))) ≤ t) :
    KPCriterion (connectedLatticePolymerSystem (d := d) (N := N) μ pe β)
      (fun c => t * (c.1.card : ℝ)) := by
  classical
  set x : ℝ := (Real.exp (|β| * B) - 1) * Real.exp t with hxdef
  have hε0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp (|β| * B) := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have hB : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hpe 1)
      positivity
    linarith
  have hx : (0 : ℝ) ≤ x := by positivity
  set S : ℝ := x / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x) with hSdef
  have hden : (0 : ℝ) < 1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * x := by
    rw [hxdef]; linarith
  have hS0 : (0 : ℝ) ≤ S := div_nonneg hx hden.le
  -- the volume-uniform per-plaquette bound
  have hthrough : ∀ p : ConcretePlaquette d N,
      (∑ Y ∈ (Finset.univ :
        Finset (connectedLatticePolymerSystem (d := d) (N := N)
          μ pe β).Polymer).filter (fun Y => p ∈ Y.1),
        x ^ Y.1.card) ≤ S := by
    intro p
    have h := sum_connectedPolymers_through_le (d := d) (N := N) p x hx
      (by rw [hxdef] at *; exact hr)
    convert h using 2
  constructor
  · intro c
    positivity
  · intro c
    have hterm : ∀ Y : (connectedLatticePolymerSystem (d := d) (N := N)
        μ pe β).Polymer,
        ‖(connectedLatticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
          Real.exp (t * (Y.1.card : ℝ)) ≤ x ^ Y.1.card := by
      intro Y
      have h1 := norm_connectedLatticePolymerSystem_activity_le
        (d := d) (N := N) μ hpe β Y
      have h2 : Real.exp (t * (Y.1.card : ℝ)) = Real.exp t ^ Y.1.card := by
        rw [mul_comm, ← Real.exp_nat_mul]
      rw [hxdef, h2, mul_pow]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    -- indicator domination: every incompatible polymer is seen through a
    -- touching plaquette
    have hdom : ∀ Y ∈ (Finset.univ :
        Finset (connectedLatticePolymerSystem (d := d) (N := N)
          μ pe β).Polymer).filter
        (fun Y => (connectedLatticePolymerSystem (d := d) (N := N)
          μ pe β).incomp c Y),
        x ^ Y.1.card ≤ ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      have hinc : ¬ Disjoint (c.1.biUnion plaquetteSupport)
          (Y.1.biUnion plaquetteSupport) := hY.2
      obtain ⟨e, hec, heY⟩ := Finset.not_disjoint_iff.mp hinc
      obtain ⟨q₀, hq₀, heq₀⟩ := Finset.mem_biUnion.mp hec
      obtain ⟨p₀, hp₀, hep₀⟩ := Finset.mem_biUnion.mp heY
      have htouch : plaquetteTouches q₀ p₀ := fun hd =>
        (Finset.disjoint_left.mp hd heq₀) hep₀
      have hp₀mem : p₀ ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q₀ p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, htouch⟩
      have hinner : x ^ Y.1.card ≤ ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q₀ p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
        have h := Finset.single_le_sum
          (f := fun p => if p ∈ Y.1 then x ^ Y.1.card else 0)
          (fun p _ => by positivity) hp₀mem
        simp only [hp₀, if_true] at h
        exact h
      refine le_trans hinner ?_
      exact Finset.single_le_sum
        (f := fun q => ∑ p ∈ (Finset.univ :
          Finset (ConcretePlaquette d N)).filter
            (fun p => plaquetteTouches q p),
          (if p ∈ Y.1 then x ^ Y.1.card else 0))
        (fun q _ => Finset.sum_nonneg fun p _ => by positivity) hq₀
    calc ∑ Y ∈ (Finset.univ :
          Finset (connectedLatticePolymerSystem (d := d) (N := N)
            μ pe β).Polymer).filter
          (fun Y => (connectedLatticePolymerSystem (d := d) (N := N)
            μ pe β).incomp c Y),
          ‖(connectedLatticePolymerSystem (d := d) (N := N) μ pe β).activity Y‖ *
            Real.exp (t * (Y.1.card : ℝ))
        ≤ ∑ Y ∈ (Finset.univ :
            Finset (connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).Polymer).filter
            (fun Y => (connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).incomp c Y),
            x ^ Y.1.card :=
          Finset.sum_le_sum fun Y _ => hterm Y
      _ ≤ ∑ Y ∈ (Finset.univ :
            Finset (connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).Polymer).filter
            (fun Y => (connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).incomp c Y),
            ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
              Finset (ConcretePlaquette d N)).filter
                (fun p => plaquetteTouches q p),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) :=
          Finset.sum_le_sum hdom
      _ ≤ ∑ Y ∈ (Finset.univ :
            Finset (connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).Polymer),
            ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
              Finset (ConcretePlaquette d N)).filter
                (fun p => plaquetteTouches q p),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun Y _ _ => Finset.sum_nonneg fun q _ =>
              Finset.sum_nonneg fun p _ => by positivity)
      _ = ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p),
            ∑ Y ∈ (Finset.univ :
              Finset (connectedLatticePolymerSystem (d := d) (N := N)
                μ pe β).Polymer),
              (if p ∈ Y.1 then x ^ Y.1.card else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
      _ = ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p),
            ∑ Y ∈ (Finset.univ :
              Finset (connectedLatticePolymerSystem (d := d) (N := N)
                μ pe β).Polymer).filter (fun Y => p ∈ Y.1),
              x ^ Y.1.card := by
          refine Finset.sum_congr rfl fun q _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ q ∈ c.1, ∑ p ∈ (Finset.univ :
            Finset (ConcretePlaquette d N)).filter
              (fun p => plaquetteTouches q p), S := by
          refine Finset.sum_le_sum fun q _ => ?_
          exact Finset.sum_le_sum fun p _ => hthrough p
      _ ≤ ∑ q ∈ c.1, ((16 * d : ℕ) : ℝ) * S := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hS0
          exact_mod_cast card_plaquettesTouching_le q
      _ = (c.1.card : ℝ) * (((16 * d : ℕ) : ℝ) * S) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (c.1.card : ℝ) * t := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hSdef, hxdef]
          exact hsmall
      _ = t * (c.1.card : ℝ) := mul_comm _ _

end UniformCriterion

end YangMills
