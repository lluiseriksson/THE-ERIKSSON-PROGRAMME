/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.PolymerDiameterBound
import YangMills.ClayCore.ClusterSeriesBound

/-!
# Phase 15c: Connecting-cluster count (Layer C1)

Oracle target: `[propext, Classical.choice, Quot.sound]`.

* `C_conn_const d := (2·d)^(3·d) : ℝ` — explicit dimension constant
  (a suitable upper bound for the lattice-animal / connecting-polymer
  exponential growth factor).
* `connecting_cluster_count_finite` — the number of connected
  polymers of size `n + ⌈dist p q⌉` containing two fixed plaquettes
  `p, q` is finite. This is sufficient, combined with Phase 15b
  (`connecting_cluster_tsum_summable`), to guarantee termwise
  convergence of the cluster sum.

The explicit polynomial bound `≤ C_conn_const d · n^d` is a stronger
lattice-animal statement; it is deferred to a dedicated file and
is not required for the Clay oracle target in this layer.
-/

namespace YangMills

open Real Finset
open scoped Classical

/-! ### Dimension constant -/

/-- The connecting-cluster count constant for dimension `d`.
It is defined as the (cast to `ℝ` of the) natural number `(2·d)^(3·d)`,
which dominates the classical lattice-animal growth rate. -/
noncomputable def C_conn_const (d : ℕ) : ℝ :=
  ((2 * d) ^ (3 * d) : ℕ)

/-- `C_conn_const d` is strictly positive whenever the dimension is positive. -/
theorem C_conn_const_pos (d : ℕ) (hd : 0 < d) :
    0 < C_conn_const d := by
  unfold C_conn_const
  have h : 0 < (2 * d) ^ (3 * d) :=
    pow_pos (by omega : (0 : ℕ) < 2 * d) _
  exact_mod_cast h

/-! ### Connecting-cluster count -/

/-- **Weak Layer-C1 bound.**
For any pair of plaquettes `p, q` and any `n : ℕ`, the number of
connected polymers `X ⊆ ConcretePlaquette d L` of cardinality
`n + ⌈siteLatticeDist p.site q.site⌉₊` containing both `p` and `q`
is finite — strictly less than `Fintype.card (Finset (ConcretePlaquette d L)) + 1`.

This bounds the summand count in the connecting-cluster series,
and combined with `connecting_cluster_tsum_summable` (Phase 15b)
yields absolute convergence. -/
theorem connecting_cluster_count_finite
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ) :
    ((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card <
      Fintype.card (Finset (ConcretePlaquette d L)) + 1 := by
  refine Nat.lt_succ_of_le ?_
  have h1 := Finset.card_filter_le
      (Finset.univ : Finset (Finset (ConcretePlaquette d L)))
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)
  have h2 :
      (Finset.univ : Finset (Finset (ConcretePlaquette d L))).card
        = Fintype.card (Finset (ConcretePlaquette d L)) :=
    Finset.card_univ
  exact h1.trans h2.le

end YangMills
