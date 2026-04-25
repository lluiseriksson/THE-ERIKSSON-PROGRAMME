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

/-- Fixed-dimension version of the shifted connecting-cluster count frontier.

This is uniform in the finite volume `L`, but its constants may depend on the
fixed lattice dimension `d`.  For the physical Clay target this is the natural
`d = 4` count frontier; it is stronger than the fixed-`d,L` audit bound and
weaker than a dimension-uniform bound over all `d`. -/
def ShiftedConnectingClusterCountBoundDim
    (d : ℕ) [NeZero d] (C_conn : ℝ) (dim : ℕ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * (((n + 1 : ℕ) : ℝ) ^ dim)

/-- Apply a fixed-dimension shifted connecting-cluster count bound to one
bucket. -/
theorem ShiftedConnectingClusterCountBoundDim.apply
    {d : ℕ} [NeZero d] {C_conn : ℝ} {dim : ℕ}
    (h : ShiftedConnectingClusterCountBoundDim d C_conn dim)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) :=
  h p q n hn hdist

/-- Finite-volume version of the shifted connecting-cluster count frontier.

This keeps `d` and `L` fixed.  Unlike the global
`ShiftedConnectingClusterCountBound`, its constants may depend on the concrete
finite plaquette lattice. -/
def ShiftedConnectingClusterCountBoundAt
    (d L : ℕ) [NeZero d] [NeZero L] (C_conn : ℝ) (dim : ℕ) : Prop :=
  ∀ (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * (((n + 1 : ℕ) : ℝ) ^ dim)

/-- Apply a finite-volume shifted connecting-cluster count package to one
bucket. -/
theorem ShiftedConnectingClusterCountBoundAt.apply
    {d L : ℕ} [NeZero d] [NeZero L] {C_conn : ℝ} {dim : ℕ}
    (h : ShiftedConnectingClusterCountBoundAt d L C_conn dim)
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) :=
  h p q n hn hdist

/-- Restrict a global shifted connecting-cluster count bound to a fixed finite
plaquette lattice. -/
theorem ShiftedConnectingClusterCountBound.toAt
    {C_conn : ℝ} {dim : ℕ}
    (h : ShiftedConnectingClusterCountBound C_conn dim)
    (d L : ℕ) [NeZero d] [NeZero L] :
    ShiftedConnectingClusterCountBoundAt d L C_conn dim := by
  intro p q n hn hdist
  exact h.apply p q n hn hdist

/-- Restrict a global shifted connecting-cluster count bound to a fixed
dimension. -/
theorem ShiftedConnectingClusterCountBound.toDim
    {C_conn : ℝ} {dim : ℕ}
    (h : ShiftedConnectingClusterCountBound C_conn dim)
    (d : ℕ) [NeZero d] :
    ShiftedConnectingClusterCountBoundDim d C_conn dim := by
  intro L _ p q n hn hdist
  exact h.apply p q n hn hdist

/-- Restrict a fixed-dimension shifted connecting-cluster count bound to a
fixed finite plaquette lattice. -/
theorem ShiftedConnectingClusterCountBoundDim.toAt
    {d : ℕ} [NeZero d] {C_conn : ℝ} {dim : ℕ}
    (h : ShiftedConnectingClusterCountBoundDim d C_conn dim)
    (L : ℕ) [NeZero L] :
    ShiftedConnectingClusterCountBoundAt d L C_conn dim := by
  intro p q n hn hdist
  exact h.apply p q n hn hdist

/-- Assemble a fixed-dimension shifted count bound from a family of
finite-volume bounds with the same constants.

This is the proof shape needed to upgrade local count estimates to the
uniform-in-volume count frontier. -/
theorem ShiftedConnectingClusterCountBoundDim.ofAtFamily
    {d : ℕ} [NeZero d] {C_conn : ℝ} {dim : ℕ}
    (h_at : ∀ (L : ℕ) [NeZero L],
      ShiftedConnectingClusterCountBoundAt d L C_conn dim) :
    ShiftedConnectingClusterCountBoundDim d C_conn dim := by
  intro L _ p q n hn hdist
  exact (h_at L).apply p q n hn hdist

/-- Packaged finite-volume shifted count data. -/
structure ShiftedF3CountPackageAt (d L : ℕ) [NeZero d] [NeZero L] where
  C_conn : ℝ
  hC : 0 < C_conn
  dim : ℕ
  h_count : ShiftedConnectingClusterCountBoundAt d L C_conn dim

/-- Packaged fixed-dimension shifted count data.

The constants are uniform in the finite volume `L`, but may depend on the fixed
lattice dimension `d`. -/
structure ShiftedF3CountPackageDim (d : ℕ) [NeZero d] where
  C_conn : ℝ
  hC : 0 < C_conn
  dim : ℕ
  h_count : ShiftedConnectingClusterCountBoundDim d C_conn dim

namespace ShiftedF3CountPackageDim

/-- Package a fixed-dimension shifted connecting-cluster count bound as the
count half at that dimension. -/
def ofBound
    (d : ℕ) [NeZero d]
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_count : ShiftedConnectingClusterCountBoundDim d C_conn dim) :
    ShiftedF3CountPackageDim d where
  C_conn := C_conn
  hC := hC
  dim := dim
  h_count := h_count

/-- Package a fixed-dimension count bound from a finite-volume family with
volume-independent constants. -/
def ofAtFamily
    (d : ℕ) [NeZero d]
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_at : ∀ (L : ℕ) [NeZero L],
      ShiftedConnectingClusterCountBoundAt d L C_conn dim) :
    ShiftedF3CountPackageDim d :=
  ofBound d C_conn hC dim
    (ShiftedConnectingClusterCountBoundDim.ofAtFamily h_at)

/-- Direct application form of a fixed-dimension shifted F3 count package. -/
theorem apply
    {d : ℕ} [NeZero d]
    (pkg : ShiftedF3CountPackageDim d)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      pkg.C_conn * (((n + 1 : ℕ) : ℝ) ^ pkg.dim) :=
  ShiftedConnectingClusterCountBoundDim.apply pkg.h_count p q n hn hdist

/-- Restrict a fixed-dimension count package to one finite plaquette lattice. -/
def toAt
    {d : ℕ} [NeZero d]
    (pkg : ShiftedF3CountPackageDim d)
    (L : ℕ) [NeZero L] :
    ShiftedF3CountPackageAt d L where
  C_conn := pkg.C_conn
  hC := pkg.hC
  dim := pkg.dim
  h_count := ShiftedConnectingClusterCountBoundDim.toAt pkg.h_count L

@[simp] theorem toAt_C_conn
    {d : ℕ} [NeZero d]
    (pkg : ShiftedF3CountPackageDim d)
    (L : ℕ) [NeZero L] :
    (pkg.toAt L).C_conn = pkg.C_conn := rfl

@[simp] theorem toAt_dim
    {d : ℕ} [NeZero d]
    (pkg : ShiftedF3CountPackageDim d)
    (L : ℕ) [NeZero L] :
    (pkg.toAt L).dim = pkg.dim := rfl

/-- Applying a fixed-dimension shifted F3 count package after restriction to a
finite plaquette lattice is definitionally the fixed-dimension bound
specialized to that volume. -/
theorem toAt_apply
    {d : ℕ} [NeZero d]
    (pkg : ShiftedF3CountPackageDim d)
    (L : ℕ) [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      (pkg.toAt L).C_conn *
        (((n + 1 : ℕ) : ℝ) ^ (pkg.toAt L).dim) :=
  (pkg.toAt L).h_count.apply p q n hn hdist

@[simp] theorem ofBound_C_conn
    (d : ℕ) [NeZero d]
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_count : ShiftedConnectingClusterCountBoundDim d C_conn dim) :
    (ofBound d C_conn hC dim h_count).C_conn = C_conn := rfl

@[simp] theorem ofBound_dim
    (d : ℕ) [NeZero d]
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_count : ShiftedConnectingClusterCountBoundDim d C_conn dim) :
    (ofBound d C_conn hC dim h_count).dim = dim := rfl

@[simp] theorem ofAtFamily_C_conn
    (d : ℕ) [NeZero d]
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_at : ∀ (L : ℕ) [NeZero L],
      ShiftedConnectingClusterCountBoundAt d L C_conn dim) :
    (ofAtFamily d C_conn hC dim h_at).C_conn = C_conn := rfl

@[simp] theorem ofAtFamily_dim
    (d : ℕ) [NeZero d]
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_at : ∀ (L : ℕ) [NeZero L],
      ShiftedConnectingClusterCountBoundAt d L C_conn dim) :
    (ofAtFamily d C_conn hC dim h_at).dim = dim := rfl

end ShiftedF3CountPackageDim

/-! ### Physical four-dimensional count target -/

/-- The physical spacetime dimension for the Clay Yang-Mills target. -/
def physicalClayDimension : ℕ := 4

/-- The physical Clay dimension is nonzero. -/
instance physicalClayDimension_neZero : NeZero physicalClayDimension := by
  dsimp [physicalClayDimension]
  infer_instance

/-- Physical, four-dimensional version of the shifted connecting-cluster count
frontier.  The constants are uniform in finite volume `L`, which is the count
input needed by the `d = 4` F3 route. -/
abbrev PhysicalShiftedConnectingClusterCountBound
    (C_conn : ℝ) (dim : ℕ) : Prop :=
  ShiftedConnectingClusterCountBoundDim physicalClayDimension C_conn dim

/-- Physical, four-dimensional finite-volume version of the shifted
connecting-cluster count audit bound.

This is local in `L`; it is not the uniform physical count frontier. -/
abbrev PhysicalShiftedConnectingClusterCountBoundAt
    (L : ℕ) [NeZero L] (C_conn : ℝ) (dim : ℕ) : Prop :=
  ShiftedConnectingClusterCountBoundAt physicalClayDimension L C_conn dim

/-- Packaged physical, four-dimensional shifted count data for the F3 route. -/
abbrev PhysicalShiftedF3CountPackage : Type :=
  ShiftedF3CountPackageDim physicalClayDimension

namespace PhysicalShiftedF3CountPackage

/-- Package a physical `d = 4` shifted connecting-cluster count bound. -/
def ofBound
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_count : PhysicalShiftedConnectingClusterCountBound C_conn dim) :
    PhysicalShiftedF3CountPackage :=
  ShiftedF3CountPackageDim.ofBound physicalClayDimension C_conn hC dim h_count

/-- Package the physical count frontier from a family of fixed-volume physical
count bounds with volume-independent constants. -/
def ofAtFamily
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_at : ∀ (L : ℕ) [NeZero L],
      PhysicalShiftedConnectingClusterCountBoundAt L C_conn dim) :
    PhysicalShiftedF3CountPackage :=
  ShiftedF3CountPackageDim.ofAtFamily physicalClayDimension
    C_conn hC dim h_at

/-- Direct application form of a physical `d = 4` shifted F3 count package. -/
theorem apply
    (pkg : PhysicalShiftedF3CountPackage)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ)
    (hn : n ∈ Finset.range
      (Fintype.card (ConcretePlaquette physicalClayDimension L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ :
      Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      pkg.C_conn * (((n + 1 : ℕ) : ℝ) ^ pkg.dim) :=
  ShiftedF3CountPackageDim.apply pkg p q n hn hdist

/-- Restrict a physical `d = 4` count package to one finite volume. -/
def toAt
    (pkg : PhysicalShiftedF3CountPackage)
    (L : ℕ) [NeZero L] :
    ShiftedF3CountPackageAt physicalClayDimension L :=
  ShiftedF3CountPackageDim.toAt pkg L

@[simp] theorem toAt_C_conn
    (pkg : PhysicalShiftedF3CountPackage)
    (L : ℕ) [NeZero L] :
    (pkg.toAt L).C_conn = pkg.C_conn := rfl

@[simp] theorem toAt_dim
    (pkg : PhysicalShiftedF3CountPackage)
    (L : ℕ) [NeZero L] :
    (pkg.toAt L).dim = pkg.dim := rfl

/-- Applying a physical shifted F3 count package after restriction to a finite
volume is definitionally the same four-dimensional count bound. -/
theorem toAt_apply
    (pkg : PhysicalShiftedF3CountPackage)
    (L : ℕ) [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ)
    (hn : n ∈ Finset.range
      (Fintype.card (ConcretePlaquette physicalClayDimension L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ :
      Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      (pkg.toAt L).C_conn *
        (((n + 1 : ℕ) : ℝ) ^ (pkg.toAt L).dim) :=
  (pkg.toAt L).h_count.apply p q n hn hdist

@[simp] theorem ofBound_C_conn
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_count : PhysicalShiftedConnectingClusterCountBound C_conn dim) :
    (ofBound C_conn hC dim h_count).C_conn = C_conn := rfl

@[simp] theorem ofBound_dim
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_count : PhysicalShiftedConnectingClusterCountBound C_conn dim) :
    (ofBound C_conn hC dim h_count).dim = dim := rfl

@[simp] theorem ofAtFamily_C_conn
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_at : ∀ (L : ℕ) [NeZero L],
      PhysicalShiftedConnectingClusterCountBoundAt L C_conn dim) :
    (ofAtFamily C_conn hC dim h_at).C_conn = C_conn := rfl

@[simp] theorem ofAtFamily_dim
    (C_conn : ℝ) (hC : 0 < C_conn) (dim : ℕ)
    (h_at : ∀ (L : ℕ) [NeZero L],
      PhysicalShiftedConnectingClusterCountBoundAt L C_conn dim) :
    (ofAtFamily C_conn hC dim h_at).dim = dim := rfl

end PhysicalShiftedF3CountPackage

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

/-- Every finite plaquette lattice has a trivial shifted count bound with
dimension `0` and constant equal to the total number of finite plaquette
subsets plus one.

This is a local finite-volume audit result, not the global uniform
lattice-animal estimate needed by F3. -/
theorem shiftedConnectingClusterCountBoundAt_finite
    (d L : ℕ) [NeZero d] [NeZero L] :
    ShiftedConnectingClusterCountBoundAt d L
      ((Fintype.card (Finset (ConcretePlaquette d L)) + 1 : ℕ) : ℝ) 0 := by
  intro p q n hn hdist
  have hlt := connecting_cluster_count_finite p q n
  have hle_nat :
      ((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
        Fintype.card (Finset (ConcretePlaquette d L)) + 1 :=
    Nat.le_of_lt hlt
  simpa using (show
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        ((Fintype.card (Finset (ConcretePlaquette d L)) + 1 : ℕ) : ℝ) by
    exact_mod_cast hle_nat)

/-- Pack the trivial finite-volume shifted count bound as reusable local count
data. -/
noncomputable def ShiftedF3CountPackageAt.finite
    (d L : ℕ) [NeZero d] [NeZero L] :
    ShiftedF3CountPackageAt d L where
  C_conn := ((Fintype.card (Finset (ConcretePlaquette d L)) + 1 : ℕ) : ℝ)
  hC := by
    exact_mod_cast (Nat.succ_pos (Fintype.card (Finset (ConcretePlaquette d L))))
  dim := 0
  h_count := shiftedConnectingClusterCountBoundAt_finite d L

@[simp] theorem ShiftedF3CountPackageAt.finite_C_conn
    (d L : ℕ) [NeZero d] [NeZero L] :
    (ShiftedF3CountPackageAt.finite d L).C_conn =
      ((Fintype.card (Finset (ConcretePlaquette d L)) + 1 : ℕ) : ℝ) := rfl

@[simp] theorem ShiftedF3CountPackageAt.finite_dim
    (d L : ℕ) [NeZero d] [NeZero L] :
    (ShiftedF3CountPackageAt.finite d L).dim = 0 := rfl

/-- Direct application form of the trivial finite-volume shifted count package.

This is intentionally local in `d,L`: its constant depends on the finite
plaquette lattice, so it is not the global uniform lattice-animal estimate
needed by F3. -/
theorem ShiftedF3CountPackageAt.finite_apply
    (d L : ℕ) [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      (ShiftedF3CountPackageAt.finite d L).C_conn *
        (((n + 1 : ℕ) : ℝ) ^ (ShiftedF3CountPackageAt.finite d L).dim) :=
  (ShiftedF3CountPackageAt.finite d L).h_count.apply p q n hn hdist

/-! ### Physical finite-volume audit count -/

/-- Packaged physical finite-volume shifted count data.

The constants may depend on the finite volume `L`; the uniform physical F3
frontier remains `PhysicalShiftedF3CountPackage`. -/
abbrev PhysicalShiftedF3CountPackageAt (L : ℕ) [NeZero L] : Type :=
  ShiftedF3CountPackageAt physicalClayDimension L

namespace PhysicalShiftedF3CountPackageAt

/-- Trivial physical finite-volume shifted count package, obtained from
finiteness of the plaquette powerset at fixed `L`. -/
noncomputable def finite
    (L : ℕ) [NeZero L] :
    PhysicalShiftedF3CountPackageAt L :=
  ShiftedF3CountPackageAt.finite physicalClayDimension L

@[simp] theorem finite_C_conn
    (L : ℕ) [NeZero L] :
    (finite L).C_conn =
      ((Fintype.card
        (Finset (ConcretePlaquette physicalClayDimension L)) + 1 : ℕ) : ℝ) :=
  rfl

@[simp] theorem finite_dim
    (L : ℕ) [NeZero L] :
    (finite L).dim = 0 := rfl

/-- Direct application form of the trivial physical finite-volume count
package.

This deliberately keeps `L` fixed, so it does not discharge the uniform
physical count frontier. -/
theorem finite_apply
    (L : ℕ) [NeZero L]
    (p q : ConcretePlaquette physicalClayDimension L) (n : ℕ)
    (hn : n ∈ Finset.range
      (Fintype.card (ConcretePlaquette physicalClayDimension L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ :
      Finset (Finset (ConcretePlaquette physicalClayDimension L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      (finite L).C_conn *
        (((n + 1 : ℕ) : ℝ) ^ (finite L).dim) :=
  ShiftedF3CountPackageAt.finite_apply physicalClayDimension L p q n hn hdist

end PhysicalShiftedF3CountPackageAt

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
#print axioms ShiftedConnectingClusterCountBoundDim.apply
#print axioms ShiftedConnectingClusterCountBoundAt.apply
#print axioms ShiftedConnectingClusterCountBound.toAt
#print axioms ShiftedConnectingClusterCountBound.toDim
#print axioms ShiftedConnectingClusterCountBoundDim.toAt
#print axioms ShiftedConnectingClusterCountBoundDim.ofAtFamily
#print axioms ShiftedF3CountPackageDim.ofBound
#print axioms ShiftedF3CountPackageDim.ofAtFamily
#print axioms ShiftedF3CountPackageDim.apply
#print axioms ShiftedF3CountPackageDim.toAt
#print axioms ShiftedF3CountPackageDim.toAt_C_conn
#print axioms ShiftedF3CountPackageDim.toAt_dim
#print axioms ShiftedF3CountPackageDim.toAt_apply
#print axioms ShiftedF3CountPackageDim.ofBound_C_conn
#print axioms ShiftedF3CountPackageDim.ofBound_dim
#print axioms ShiftedF3CountPackageDim.ofAtFamily_C_conn
#print axioms ShiftedF3CountPackageDim.ofAtFamily_dim
#print axioms physicalClayDimension
#print axioms PhysicalShiftedF3CountPackage.ofBound
#print axioms PhysicalShiftedF3CountPackage.ofAtFamily
#print axioms PhysicalShiftedF3CountPackage.apply
#print axioms PhysicalShiftedF3CountPackage.toAt
#print axioms PhysicalShiftedF3CountPackage.toAt_C_conn
#print axioms PhysicalShiftedF3CountPackage.toAt_dim
#print axioms PhysicalShiftedF3CountPackage.toAt_apply
#print axioms PhysicalShiftedF3CountPackage.ofBound_C_conn
#print axioms PhysicalShiftedF3CountPackage.ofBound_dim
#print axioms PhysicalShiftedF3CountPackage.ofAtFamily_C_conn
#print axioms PhysicalShiftedF3CountPackage.ofAtFamily_dim
#print axioms shiftedConnectingClusterCountBoundAt_finite
#print axioms ShiftedF3CountPackageAt.finite
#print axioms ShiftedF3CountPackageAt.finite_C_conn
#print axioms ShiftedF3CountPackageAt.finite_dim
#print axioms ShiftedF3CountPackageAt.finite_apply
#print axioms PhysicalShiftedF3CountPackageAt.finite
#print axioms PhysicalShiftedF3CountPackageAt.finite_C_conn
#print axioms PhysicalShiftedF3CountPackageAt.finite_dim
#print axioms PhysicalShiftedF3CountPackageAt.finite_apply

end YangMills
