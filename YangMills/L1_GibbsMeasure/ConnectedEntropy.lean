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

end YangMills
