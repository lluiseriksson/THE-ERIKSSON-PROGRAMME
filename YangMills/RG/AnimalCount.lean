/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# The bounded-degree walk-count engine (gauge-RG, `hRpoly` campaign brick P1a)

`docs/HRPOLY-CAMPAIGN-PLAN.md` brick **P1**.  The geometric summability
input of the cluster-expansion-with-holes (branch C of `hRpoly`) reduces
to the **lattice animal count** `c_n ≤ Cⁿ` — the number of connected
`n`-polymers containing a fixed cube is at most `Cⁿ`.  The standard route
to that geometric bound encodes a connected size-`n` set as a
depth-first-search **walk** of bounded length on the cube-adjacency
graph; the number of such walks is what this file's engine controls.

**This brick (P1a).**  For any `SimpleGraph` of maximum degree `≤ Δ`, the
total number of length-`n` walks starting at a fixed vertex `u` is `≤ Δⁿ`:
`∑_v #{p : Walk u v | p.length = n} ≤ Δⁿ`.

Proof: induction on `n` through Mathlib's recursive `Finset` description
`finsetWalkLength (n+1) u v = ⋃_{w ∈ N(u)} cons '' (finsetWalkLength n w v)`,
together with `Finset.card_biUnion_le`, `Finset.card_map`,
`Finset.sum_comm`, and `card_neighborSet_eq_degree`.  Pure graph
combinatorics — no measure theory, no cluster expansion.  Reusable
engine; the documented consumer is the animal-count brick P1b feeding
`RG.polymer_weight_summability`.

**Source.**  Standard self-avoiding-walk / lattice-animal counting (e.g.
Madras–Slade, *The Self-Avoiding Walk*); strategy/framing Lluis Eriksson
(ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

open Finset

namespace YangMills.RG

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One RG step of the walk recursion: a length-`(n+1)` walk from `u` is a
choice of neighbour `w` of `u` followed by a length-`n` walk from `w`, so
its count is bounded by the per-neighbour sum of length-`n` walk counts.
This is `Finset.card_biUnion_le` applied to Mathlib's recursive
description of `finsetWalkLength`. -/
theorem card_finsetWalkLength_succ_le (n : ℕ) (u v : V) :
    (G.finsetWalkLength (n + 1) u v).card
      ≤ ∑ w : G.neighborSet u, (G.finsetWalkLength n (w : V) v).card := by
  simp only [finsetWalkLength]
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum (fun w _ => (Finset.card_map _).le)

/-- **Bounded-degree walk count.**  If every vertex of `G` has degree
`≤ Δ`, then the total number of length-`n` walks starting at a fixed
vertex `u` is at most `Δⁿ`.  The engine behind the lattice animal-count
bound `c_n ≤ Cⁿ` (campaign brick P1). -/
theorem card_walks_length_le_degree_pow {Δ : ℕ}
    (hΔ : ∀ w, G.degree w ≤ Δ) (n : ℕ) (u : V) :
    ∑ v, (G.finsetWalkLength n u v).card ≤ Δ ^ n := by
  induction n generalizing u with
  | zero =>
    have h1 : ∀ v, (G.finsetWalkLength 0 u v).card = if u = v then 1 else 0 := by
      intro v
      rcases eq_or_ne u v with h | h
      · subst h; simp [finsetWalkLength]
      · simp [finsetWalkLength, h]
    simp only [h1]
    rw [Finset.sum_ite_eq]
    simp
  | succ n ih =>
    calc ∑ v, (G.finsetWalkLength (n + 1) u v).card
        ≤ ∑ v, ∑ w : G.neighborSet u, (G.finsetWalkLength n (w : V) v).card :=
          Finset.sum_le_sum (fun v _ => card_finsetWalkLength_succ_le G n u v)
      _ = ∑ w : G.neighborSet u, ∑ v, (G.finsetWalkLength n (w : V) v).card :=
          Finset.sum_comm
      _ ≤ ∑ _w : G.neighborSet u, Δ ^ n :=
          Finset.sum_le_sum (fun w _ => ih (w : V))
      _ = G.degree u * Δ ^ n := by
          rw [Finset.sum_const, Finset.card_univ, card_neighborSet_eq_degree,
            nsmul_eq_mul, Nat.cast_id]
      _ ≤ Δ ^ (n + 1) := by
          rw [pow_succ']
          gcongr
          exact hΔ u

end YangMills.RG
