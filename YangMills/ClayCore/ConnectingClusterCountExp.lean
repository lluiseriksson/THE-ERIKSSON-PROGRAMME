/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.ConnectingClusterCount

/-!
# Exponential connecting-cluster count frontier

This file records the KP/lattice-animal count shape with an exponential
bucket profile `C_conn * K^n`.

The existing polynomial frontier in `ConnectingClusterCount.lean` is kept
intact for downstream compatibility.  This module is additive: it names the
classical exponential count interface and provides the same global /
fixed-dimension / fixed-volume package projections.

The finite-volume canary below is intentionally local in `L`; it is not the
uniform F3 count theorem.
-/

namespace YangMills

open Real Finset
open scoped Classical

/-! ### Exponential connecting-cluster count frontiers -/

/-- Global exponential shifted lattice-animal bucket-count frontier.

It is uniform in lattice dimension `d` and finite volume `L`. -/
def ShiftedConnectingClusterCountBoundExp (C_conn K : ℝ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * K ^ n

/-- Apply a global exponential count bound to one bucket. -/
theorem ShiftedConnectingClusterCountBoundExp.apply
    {C_conn K : ℝ}
    (h : ShiftedConnectingClusterCountBoundExp C_conn K)
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * K ^ n :=
  h p q n hn hdist

/-- Fixed-dimension exponential shifted count frontier, uniform in volume. -/
def ShiftedConnectingClusterCountBoundDimExp
    (d : ℕ) [NeZero d] (C_conn K : ℝ) : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * K ^ n

/-- Apply a fixed-dimension exponential count bound to one bucket. -/
theorem ShiftedConnectingClusterCountBoundDimExp.apply
    {d : ℕ} [NeZero d] {C_conn K : ℝ}
    (h : ShiftedConnectingClusterCountBoundDimExp d C_conn K)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * K ^ n :=
  h p q n hn hdist

/-- Fixed finite-volume exponential shifted count frontier.

Constants may depend on both `d` and `L`; this is an audit/local interface,
not the uniform F3 count theorem. -/
def ShiftedConnectingClusterCountBoundAtExp
    (d L : ℕ) [NeZero d] [NeZero L] (C_conn K : ℝ) : Prop :=
  ∀ (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * K ^ n

/-- Apply a finite-volume exponential count bound to one bucket. -/
theorem ShiftedConnectingClusterCountBoundAtExp.apply
    {d L : ℕ} [NeZero d] [NeZero L] {C_conn K : ℝ}
    (h : ShiftedConnectingClusterCountBoundAtExp d L C_conn K)
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * K ^ n :=
  h p q n hn hdist

/-- Restrict a global exponential count bound to a fixed dimension. -/
theorem ShiftedConnectingClusterCountBoundExp.toDim
    {C_conn K : ℝ}
    (h : ShiftedConnectingClusterCountBoundExp C_conn K)
    (d : ℕ) [NeZero d] :
    ShiftedConnectingClusterCountBoundDimExp d C_conn K := by
  intro L _ p q n hn hdist
  exact h.apply p q n hn hdist

/-- Restrict a global exponential count bound to a fixed finite volume. -/
theorem ShiftedConnectingClusterCountBoundExp.toAt
    {C_conn K : ℝ}
    (h : ShiftedConnectingClusterCountBoundExp C_conn K)
    (d L : ℕ) [NeZero d] [NeZero L] :
    ShiftedConnectingClusterCountBoundAtExp d L C_conn K := by
  intro p q n hn hdist
  exact h.apply p q n hn hdist

/-- Restrict a fixed-dimension exponential count bound to one finite volume. -/
theorem ShiftedConnectingClusterCountBoundDimExp.toAt
    {d : ℕ} [NeZero d] {C_conn K : ℝ}
    (h : ShiftedConnectingClusterCountBoundDimExp d C_conn K)
    (L : ℕ) [NeZero L] :
    ShiftedConnectingClusterCountBoundAtExp d L C_conn K := by
  intro p q n hn hdist
  exact h.apply p q n hn hdist

/-! ### Packaged exponential count data -/

/-- Global packaged exponential count data. -/
structure ShiftedF3CountPackageExp where
  C_conn : ℝ
  K : ℝ
  hC : 0 < C_conn
  hK : 0 < K
  h_count : ShiftedConnectingClusterCountBoundExp C_conn K

namespace ShiftedF3CountPackageExp

/-- Package a global exponential count bound. -/
def ofBound
    (C_conn K : ℝ) (hC : 0 < C_conn) (hK : 0 < K)
    (h_count : ShiftedConnectingClusterCountBoundExp C_conn K) :
    ShiftedF3CountPackageExp where
  C_conn := C_conn
  K := K
  hC := hC
  hK := hK
  h_count := h_count

/-- Apply a global exponential count package to one bucket. -/
theorem apply
    (pkg : ShiftedF3CountPackageExp)
    {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      pkg.C_conn * pkg.K ^ n :=
  ShiftedConnectingClusterCountBoundExp.apply pkg.h_count p q n hn hdist

end ShiftedF3CountPackageExp

/-- Fixed-dimension packaged exponential count data. -/
structure ShiftedF3CountPackageDimExp (d : ℕ) [NeZero d] where
  C_conn : ℝ
  K : ℝ
  hC : 0 < C_conn
  hK : 0 < K
  h_count : ShiftedConnectingClusterCountBoundDimExp d C_conn K

namespace ShiftedF3CountPackageDimExp

/-- Package a fixed-dimension exponential count bound. -/
def ofBound
    (d : ℕ) [NeZero d]
    (C_conn K : ℝ) (hC : 0 < C_conn) (hK : 0 < K)
    (h_count : ShiftedConnectingClusterCountBoundDimExp d C_conn K) :
    ShiftedF3CountPackageDimExp d where
  C_conn := C_conn
  K := K
  hC := hC
  hK := hK
  h_count := h_count

/-- Package a fixed-dimension exponential count bound from a uniform family of
finite-volume exponential count bounds. -/
def ofAtFamily
    (d : ℕ) [NeZero d]
    (C_conn K : ℝ) (hC : 0 < C_conn) (hK : 0 < K)
    (h_at : ∀ (L : ℕ) [NeZero L],
      ShiftedConnectingClusterCountBoundAtExp d L C_conn K) :
    ShiftedF3CountPackageDimExp d where
  C_conn := C_conn
  K := K
  hC := hC
  hK := hK
  h_count := by
    intro L _ p q n hn hdist
    exact (h_at L).apply p q n hn hdist

/-- Apply a fixed-dimension exponential count package to one bucket. -/
theorem apply
    {d : ℕ} [NeZero d]
    (pkg : ShiftedF3CountPackageDimExp d)
    {L : ℕ} [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      pkg.C_conn * pkg.K ^ n :=
  ShiftedConnectingClusterCountBoundDimExp.apply pkg.h_count p q n hn hdist

end ShiftedF3CountPackageDimExp

/-! ### Fixed-volume packaged exponential count data -/

/-- Fixed finite-volume packaged exponential count data. -/
structure ShiftedF3CountPackageAtExp
    (d L : ℕ) [NeZero d] [NeZero L] where
  C_conn : ℝ
  K : ℝ
  hC : 0 < C_conn
  hK : 0 < K
  h_count : ShiftedConnectingClusterCountBoundAtExp d L C_conn K

namespace ShiftedF3CountPackageAtExp

/-- Apply a fixed-volume exponential count package to one bucket. -/
theorem apply
    {d L : ℕ} [NeZero d] [NeZero L]
    (pkg : ShiftedF3CountPackageAtExp d L)
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      pkg.C_conn * pkg.K ^ n :=
  ShiftedConnectingClusterCountBoundAtExp.apply pkg.h_count p q n hn hdist

end ShiftedF3CountPackageAtExp

/-! ### Physical four-dimensional exponential count route -/

/-- Physical `d = 4` exponential count frontier. -/
abbrev PhysicalShiftedConnectingClusterCountBoundExp
    (C_conn K : ℝ) : Prop :=
  ShiftedConnectingClusterCountBoundDimExp physicalClayDimension C_conn K

/-- Physical finite-volume exponential count audit frontier. -/
abbrev PhysicalShiftedConnectingClusterCountBoundAtExp
    (L : ℕ) [NeZero L] (C_conn K : ℝ) : Prop :=
  ShiftedConnectingClusterCountBoundAtExp physicalClayDimension L C_conn K

/-- Packaged physical `d = 4` exponential count data. -/
abbrev PhysicalShiftedF3CountPackageExp : Type :=
  ShiftedF3CountPackageDimExp physicalClayDimension

namespace PhysicalShiftedF3CountPackageExp

/-- Package a physical exponential count bound. -/
def ofBound
    (C_conn K : ℝ) (hC : 0 < C_conn) (hK : 0 < K)
    (h_count : PhysicalShiftedConnectingClusterCountBoundExp C_conn K) :
    PhysicalShiftedF3CountPackageExp :=
  ShiftedF3CountPackageDimExp.ofBound physicalClayDimension
    C_conn K hC hK h_count

/-- Package a physical exponential count bound from a volume-uniform family of
finite-volume physical bounds. -/
def ofAtFamily
    (C_conn K : ℝ) (hC : 0 < C_conn) (hK : 0 < K)
    (h_at : ∀ (L : ℕ) [NeZero L],
      PhysicalShiftedConnectingClusterCountBoundAtExp L C_conn K) :
    PhysicalShiftedF3CountPackageExp :=
  ShiftedF3CountPackageDimExp.ofAtFamily physicalClayDimension
    C_conn K hC hK h_at

/-- Apply a physical exponential count package to one bucket. -/
theorem apply
    (pkg : PhysicalShiftedF3CountPackageExp)
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
      pkg.C_conn * pkg.K ^ n :=
  ShiftedF3CountPackageDimExp.apply pkg p q n hn hdist

end PhysicalShiftedF3CountPackageExp

/-! ### Finite-volume canaries -/

/-- A fixed finite volume has a trivial local exponential count bound with
`K = 1` and volume-dependent `C_conn`. -/
theorem shiftedConnectingClusterCountBoundAtExp_finite
    (d L : ℕ) [NeZero d] [NeZero L] :
    ShiftedConnectingClusterCountBoundAtExp d L
      ((Fintype.card (Finset (ConcretePlaquette d L)) + 1 : ℕ) : ℝ) 1 := by
  intro p q n hn hdist
  have hlt :=
    connecting_cluster_count_finite (d := d) (L := L) p q n
  have hle_nat :
      ((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card ≤
        Fintype.card (Finset (ConcretePlaquette d L)) + 1 :=
    Nat.le_of_lt hlt
  have hle_real :
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun X =>
          p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
            X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        ((Fintype.card (Finset (ConcretePlaquette d L)) + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hle_nat
  simpa using hle_real

/-- Packaged fixed-volume exponential count canary. -/
def ShiftedF3CountPackageAtExp_finite
    (d L : ℕ) [NeZero d] [NeZero L] :
    ShiftedF3CountPackageAtExp d L where
  C_conn := ((Fintype.card (Finset (ConcretePlaquette d L)) + 1 : ℕ) : ℝ)
  K := 1
  hC := by
    exact_mod_cast (Nat.succ_pos (Fintype.card (Finset (ConcretePlaquette d L))))
  hK := one_pos
  h_count := shiftedConnectingClusterCountBoundAtExp_finite d L

#print axioms ShiftedConnectingClusterCountBoundExp.apply
#print axioms ShiftedConnectingClusterCountBoundDimExp.apply
#print axioms ShiftedConnectingClusterCountBoundAtExp.apply
#print axioms ShiftedConnectingClusterCountBoundExp.toDim
#print axioms ShiftedConnectingClusterCountBoundExp.toAt
#print axioms ShiftedConnectingClusterCountBoundDimExp.toAt
#print axioms ShiftedF3CountPackageExp.ofBound
#print axioms ShiftedF3CountPackageExp.apply
#print axioms ShiftedF3CountPackageDimExp.ofBound
#print axioms ShiftedF3CountPackageDimExp.ofAtFamily
#print axioms ShiftedF3CountPackageDimExp.apply
#print axioms ShiftedF3CountPackageAtExp.apply
#print axioms PhysicalShiftedF3CountPackageExp.ofBound
#print axioms PhysicalShiftedF3CountPackageExp.ofAtFamily
#print axioms PhysicalShiftedF3CountPackageExp.apply
#print axioms shiftedConnectingClusterCountBoundAtExp_finite
#print axioms ShiftedF3CountPackageAtExp_finite

end YangMills
