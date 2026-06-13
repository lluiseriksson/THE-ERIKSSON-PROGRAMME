/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.AnimalTour

/-!
# The `M`-cube adjacency graph and concrete lattice polymer summability
(gauge-RG, `hRpoly` campaign — P2 geometry)

`docs/HRPOLY-CAMPAIGN-PLAN.md`, `docs/BALABAN-SOURCE-BOUNDS.md`.  Dimock II
(arXiv:1212.5562) §3.1.2 defines a **polymer** as a connected union of
`M`-cubes, where two `M`-cubes are adjacent iff they share a boundary of any
dimension (face/edge/vertex) — the **king-move / Chebyshev (`ℓ^∞`)
adjacency**, with coordination number `3^d − 1` (`= 26` for `d = 3`).  The
source also notes that a spanning tree on `n` such cubes is explored by a walk
of `≤ 2n` steps and the number of size-`n` polymers containing a fixed cube is
`≤ cⁿ` with `c ∝ 3^d − 1` — which is exactly the content of
`RG/AnimalTour.lean` (`exists_spanning_closed_walk`, `animal_card_le`).

This file makes that geometry concrete:

* **`cubeAdj d L`** — the `M`-cube king-adjacency `SimpleGraph` on the
  `d`-dimensional torus `(ZMod L)^d`.
* **`cubeAdj_degree_le`** — the degree bound `≤ 3^d` (the `3^d − 1`
  coordination plus trivial slack), via the displacement injection
  `y ↦ (i ↦ y i − x i) ∈ {0,1,−1}^d`.
* **`cube_polymer_summable`** — instantiating `rooted_connected_weight_summable`
  on `cubeAdj`: the geometric summability `∑_Y q^{#Y} ≤ (1 − (3^d)²q)⁻¹` for
  `(3^d)²q < 1`, on Dimock's actual lattice geometry with the explicit
  coordination constant.

**Honest scope.**  This is the **bulk / hole-free** geometric summability
(the `Ω^c = ∅` case of Dimock II's eq. 151).  The full *modified-metric*
summability `∑_{X⊇□} e^{−κ₀ d_M(X, mod Ω^c)} ≤ K₀` with large-field holes
additionally requires the holes' Gaussian suppression and is NOT covered here.
This also formalises the lattice *combinatorics*; the §3.14 raw activity
*bound* and the Appendix F cluster-expansion-with-holes (P3/P4) — and the fact
that Dimock's constants are for `φ⁴₃`, not 4D Yang–Mills — remain open
(`docs/BALABAN-SOURCE-BOUNDS.md`).

**Source.**  Dimock II (arXiv:1212.5562) §3.1.2; Madras–Slade (animal
counting); strategy/framing Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open Finset

namespace YangMills.RG

open SimpleGraph

/-- The `M`-cube **king-adjacency** graph on `(ZMod L)^d`: two cubes are
adjacent iff they differ by `0` or `±1` in every coordinate and are distinct
(Chebyshev/`ℓ^∞` distance `1`).  Dimock II §3.1.2's `M`-cube adjacency;
coordination number `3^d − 1`. -/
def cubeAdj (d L : ℕ) : SimpleGraph (Fin d → ZMod L) where
  Adj x y := x ≠ y ∧ ∀ i, y i - x i = 0 ∨ y i - x i = 1 ∨ y i - x i = -1
  symm := by
    rintro x y ⟨hne, hd⟩
    refine ⟨hne.symm, fun i => ?_⟩
    have hxy : x i - y i = -(y i - x i) := (neg_sub _ _).symm
    rcases hd i with h | h | h
    · left; rw [hxy, h, neg_zero]
    · right; right; rw [hxy, h]
    · right; left; rw [hxy, h, neg_neg]
  loopless := ⟨fun x hx => hx.1 rfl⟩

instance (d L : ℕ) : DecidableRel (cubeAdj d L).Adj := by
  intro x y
  show Decidable (x ≠ y ∧ ∀ i, y i - x i = 0 ∨ y i - x i = 1 ∨ y i - x i = -1)
  infer_instance

/-- **Bounded degree of the `M`-cube adjacency**: every cube has at most `3^d`
neighbours.  Each neighbour `y` is determined by its displacement
`i ↦ y i − x i ∈ {0,1,−1}`, an injection into `Fin d → {0,1,−1}` of
cardinality `≤ 3^d`.  Supplies the degree bound `Δ = 3^d` for the lattice
animal count / geometric summability on Dimock's polymer geometry. -/
theorem cubeAdj_degree_le (d L : ℕ) [NeZero L] (x : Fin d → ZMod L) :
    (cubeAdj d L).degree x ≤ 3 ^ d := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc ((cubeAdj d L).neighborFinset x).card
      ≤ (Fintype.piFinset (fun _ : Fin d => ({0, 1, -1} : Finset (ZMod L)))).card := by
        refine Finset.card_le_card_of_injOn (fun y i => y i - x i) ?_ ?_
        · intro y hy
          simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy
          simp only [Finset.mem_coe, Fintype.mem_piFinset]
          intro i
          rcases hy.2 i with h | h | h <;> simp [h]
        · intro y _ y' _ h
          funext i
          have hi : y i - x i = y' i - x i := congrFun h i
          have := congrArg (· + x i) hi
          simpa using this
    _ = ∏ _i : Fin d, ({0, 1, -1} : Finset (ZMod L)).card := Fintype.card_piFinset _
    _ ≤ 3 ^ d := by
        refine le_trans (Finset.prod_le_pow_card _ _ 3 (fun i _ => ?_)) ?_
        · calc ({0, 1, -1} : Finset (ZMod L)).card
              ≤ ({1, -1} : Finset (ZMod L)).card + 1 := Finset.card_insert_le _ _
            _ ≤ (({-1} : Finset (ZMod L)).card + 1) + 1 := by
                gcongr; exact Finset.card_insert_le _ _
            _ = 3 := by simp
        · rw [Finset.card_univ, Fintype.card_fin]

/-- **Concrete cube-lattice polymer summability**: instantiating the abstract
branch-C bound on Dimock's `M`-cube king-adjacency graph.  With decay `q`
satisfying `(3^d)²·q < 1`, the size-graded weight sum over all connected
polymers (in the `3^d`-coordination adjacency) rooted at a fixed cube `r`
converges to `(1 − (3^d)²q)⁻¹`.  The geometric summability substrate of
`hRpoly` branch C, on the actual lattice geometry, with the explicit
coordination-number constant `Δ = 3^d`.  (Bulk / hole-free case; see header.) -/
theorem cube_polymer_summable (d L : ℕ) [NeZero L] (r : Fin d → ZMod L) {q : ℝ}
    (hq0 : 0 ≤ q) (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * q < 1) :
    ∑' Y : {S : Finset (Fin d → ZMod L) //
        r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w},
        q ^ (Y : Finset (Fin d → ZMod L)).card
      ≤ (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * q)⁻¹ :=
  rooted_connected_weight_summable (G := cubeAdj d L)
    (fun x => cubeAdj_degree_le d L x) (Nat.one_le_pow _ _ (by norm_num)) hq0 hCq

end YangMills.RG
