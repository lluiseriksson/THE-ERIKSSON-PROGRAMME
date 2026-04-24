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

/-- `C_conn_const d` is strictly positive for a nonzero dimension. -/
theorem C_conn_const_pos_of_neZero (d : ℕ) [NeZero d] :
    0 < C_conn_const d := by
  have hd : 0 < d := by
    have hne : d ≠ 0 := NeZero.ne d
    omega
  exact C_conn_const_pos d hd

/-! ### Connecting-cluster count -/

/-- The shifted lattice-animal bucket-count frontier used by the preferred
F3 endpoint.

It states that the number of connected polymers of cardinality
`n + ⌈dist(p,q)⌉₊` containing both marked plaquettes is bounded by the
non-vacuous polynomial profile `C_conn * (n+1)^dim`.  This is the exact
combinatorial target consumed by
`clay_theorem_of_count_connectedCardDecayActivities_ceil_shifted`. -/
def ShiftedConnectingClusterCountBound (C_conn : ℝ) (dim : ℕ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * (((n + 1 : ℕ) : ℝ) ^ dim)

/-- Apply a shifted connecting-cluster count package to one bucket. -/
theorem ShiftedConnectingClusterCountBound.apply
    {C_conn : ℝ} {dim : ℕ}
    (h : ShiftedConnectingClusterCountBound C_conn dim)
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) :=
  h p q n hn hdist

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

/-- Any connected polymer containing `p` and `q` lies in a canonical
distance-indexed cardinality bucket: its size is an "extra size" `n`
plus the ceiling of the lattice distance between `p` and `q`.

This is the exact natural-number decomposition used by the F3
connecting-cluster series
`n + ⌈siteLatticeDist p.site q.site⌉₊`. -/
theorem connected_polymer_card_eq_extra_add_dist
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L)
    (X : Finset (ConcretePlaquette d L))
    (hpX : p ∈ X) (hqX : q ∈ X) (hconn : PolymerConnected X) :
    ∃ n : ℕ, X.card = n + ⌈siteLatticeDist p.site q.site⌉₊ := by
  have hceil_le :
      ⌈siteLatticeDist p.site q.site⌉₊ ≤ X.card :=
    ceil_siteLatticeDist_le_polymer_card p q X hpX hqX hconn
  use X.card - ⌈siteLatticeDist p.site q.site⌉₊
  omega

#print axioms connecting_cluster_count_finite
#print axioms connected_polymer_card_eq_extra_add_dist
#print axioms C_conn_const_pos_of_neZero
#print axioms ShiftedConnectingClusterCountBound.apply

end YangMills
