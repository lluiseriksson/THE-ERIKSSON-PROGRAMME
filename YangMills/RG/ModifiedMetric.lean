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
  of the polymer the modified metric `d_M` actually weights.
* **`cubeConnected`** — the walk-based form of "connected polymer" (the
  self-contained idiom of `RG/AnimalTour.lean`, avoiding the
  `Set`/`Finset` `SimpleGraph.Connected` API).
* **`walk_crosses_frontier`** — the elementary bridge lemma: a walk that
  stays in `A ∪ B`, starts in `A \ B` and ends in `B \ A`, must cross an
  `Adj`-edge from `A` to `B`.  Proved by induction on the walk.
* **`absorbedHole_touches_skeleton_single`** — the combinatorial heart of
  Dimock Lemma E.3, **single-hole case** `X = Y ∪ H₀`: if `X` is
  `cubeConnected` with `Y`, `H₀` nonempty and disjoint, then `H₀` touches
  `Y` via a `cubeAdj`-edge.  This is exactly the step by which Dimock bounds
  the number of absorbable holes by the *per-cube frontier* of the skeleton
  (rather than the global hole family), turning a hole-discounted decay into
  a uniform polymer count.

## What is NOT here (honest scope)

* The full multi-hole hole-multiplicity bound `#{X : skeleton = Y} ≤
  2^{2d·|Y|}` (Dimock eq. ~630), the sharp `2d` face-coordination, and the
  eq-151 summability with the Gaussian suppression are **open** (P4,
  months-scale).  This file supplies the single-hole touching lemma (fully
  rigorous); the multi-hole assembly, the per-cube frontier count, and the
  analytic `e^{−c|Ω_k^c|_M}` suppression remain.
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

/-- A cube-set `S` is **walk-connected** in `cubeAdj` (the walk-based form of
connectivity used throughout `RG/AnimalTour.lean`): every vertex of `S` is
reachable from every other by a `cubeAdj`-walk staying inside `S`.  This is
the self-contained form of "connected polymer" avoiding the `Set`-vs-`Finset`
`SimpleGraph.Connected` API. -/
def cubeConnected {d L : ℕ} (S : Finset (Cube d L)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ w : (cubeAdj d L).Walk x y, ∀ v ∈ w.support, v ∈ S

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

end YangMills.RG
