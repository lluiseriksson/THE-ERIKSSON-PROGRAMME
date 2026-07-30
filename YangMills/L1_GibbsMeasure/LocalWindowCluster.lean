/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalWindowActivity

/-!
# Stability of local polymer-cluster terms across finite volumes

A `WindowPolymer` is a nonempty connected finite set of plaquettes in the
volume-independent common window.  Its realizations in any two fitting tori
have:

* identical activities;
* identical incompatibility relations;
* consequently identical Ursell coefficients and cluster monomials.

This is still an exact free-gas statement.  It does not identify normalized
Gibbs expectations: the terms whose polymers leave the common window remain
to be bounded by the volume-uniform pinned KP tail.
-/

namespace YangMills

open MeasureTheory GaugeConfig

/-- The weighted system specialized to the Wilson Mayer weight is
definitionally the connected lattice system used by the volume-uniform KP
tail theorem. -/
theorem weightedLatticePolymerSystem_plaquetteWeight
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ) :
    weightedLatticePolymerSystem (d := d) (N := N) μ
        (fun A p => plaquetteWeight pe β A p)
      =
    connectedLatticePolymerSystem (d := d) (N := N) μ pe β := rfl

/-- A volume-independent connected lattice polymer. -/
structure WindowPolymer (d : ℕ) where
  support : Finset (WindowPlaquette d)
  nonempty : support.Nonempty
  connected : WindowPlaquette.IsConnectedPolymer support

namespace WindowPolymer

/-- Every plaquette of the abstract polymer fits in a side-`N` torus. -/
def Fits {d : ℕ} (c : WindowPolymer d) (N : ℕ) : Prop :=
  ∀ p ∈ c.support, p.Fits N

/-- Positive-edge support of an abstract window polymer. -/
def edgeSupport {d : ℕ} (c : WindowPolymer d) :
    Finset (WindowPosEdge d) :=
  WindowPlaquette.edgeSupport c.support

/-- Abstract incompatibility: the two positive-edge supports overlap. -/
def Incompatible {d : ℕ} (c c' : WindowPolymer d) : Prop :=
  ¬ Disjoint c.edgeSupport c'.edgeSupport

/-- Realization of a window polymer in the weighted connected lattice gas. -/
noncomputable def toWeightedPolymer
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : WindowPolymer d) (h : c.Fits N) :
    (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer := by
  refine ⟨WindowPlaquette.realizedFinset c.support h, ?_⟩
  constructor
  · obtain ⟨p, hp⟩ := c.nonempty
    exact ⟨p.toConcrete (h p hp),
      WindowPlaquette.mem_realizedFinset_iff.mpr
        ⟨⟨p, hp⟩, rfl⟩⟩
  · exact
      (WindowPlaquette.isConnectedPolymer_realizedFinset_iff
        c.support h).mp c.connected

@[simp]
theorem toWeightedPolymer_val
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : WindowPolymer d) (h : c.Fits N) :
    (c.toWeightedPolymer μ w h).1 =
      WindowPlaquette.realizedFinset c.support h := rfl

/-- Realizing an abstract incompatibility gives precisely the finite-volume
polymer-system incompatibility relation. -/
theorem incomp_toWeightedPolymer_iff
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c c' : WindowPolymer d) (hc : c.Fits N) (hc' : c'.Fits N) :
    (weightedLatticePolymerSystem (d := d) (N := N) μ w).incomp
        (c.toWeightedPolymer μ w hc)
        (c'.toWeightedPolymer μ w hc') ↔
      c.Incompatible c' := by
  change ¬ Disjoint
      ((WindowPlaquette.realizedFinset c.support hc).biUnion
        plaquetteSupport)
      ((WindowPlaquette.realizedFinset c'.support hc').biUnion
        plaquetteSupport) ↔
    ¬ Disjoint c.edgeSupport c'.edgeSupport
  rw [WindowPlaquette.biUnion_support_realizedFinset hc,
    WindowPlaquette.biUnion_support_realizedFinset hc']
  exact not_congr
    (WindowPosEdge.disjoint_realizedFinset_iff
      (WindowPlaquette.edgeSupport_fits hc)
      (WindowPlaquette.edgeSupport_fits hc'))

/-- The activity of a window polymer is literally the same number in every
two fitting volumes. -/
theorem activity_toWeightedPolymer_eq
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (c : WindowPolymer d) (hN : c.Fits N) (hM : c.Fits M) :
    (weightedLatticePolymerSystem (d := d) (N := N) μ
      (fun A p => plaquetteWeight pe β A p)).activity
        (c.toWeightedPolymer μ
          (N := N)
          (fun (A : GaugeConfig d N G) (p : ConcretePlaquette d N) =>
            plaquetteWeight pe β A p) hN)
      =
    (weightedLatticePolymerSystem (d := d) (N := M) μ
      (fun A p => plaquetteWeight pe β A p)).activity
        (c.toWeightedPolymer μ
          (N := M)
          (fun (A : GaugeConfig d M G) (p : ConcretePlaquette d M) =>
            plaquetteWeight pe β A p) hM) := by
  change
    ((∫ A, ∏ p ∈ WindowPlaquette.realizedFinset c.support hN,
        plaquetteWeight pe β A p
      ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ)
      =
    ((∫ A, ∏ p ∈ WindowPlaquette.realizedFinset c.support hM,
        plaquetteWeight pe β A p
      ∂(gaugeMeasureFrom (d := d) (N := M) μ) : ℝ) : ℂ)
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  have hcastN :
      (fun A : GaugeConfig d N G =>
        ((∏ p ∈ WindowPlaquette.realizedFinset c.support hN,
          plaquetteWeight pe β A p : ℝ) : ℂ))
        =
      fun A => ∏ p ∈ WindowPlaquette.realizedFinset c.support hN,
        (plaquetteWeight pe β A p : ℂ) := by
    funext A
    push_cast
    rfl
  have hcastM :
      (fun A : GaugeConfig d M G =>
        ((∏ p ∈ WindowPlaquette.realizedFinset c.support hM,
          plaquetteWeight pe β A p : ℝ) : ℂ))
        =
      fun A => ∏ p ∈ WindowPlaquette.realizedFinset c.support hM,
        (plaquetteWeight pe β A p : ℂ) := by
    funext A
    push_cast
    rfl
  rw [hcastN, hcastM]
  exact integral_prod_plaquetteWeight_realizedFinset_eq
    μ pe β c.support hN hM

end WindowPolymer

namespace KP

/-- Ursell coefficients depend only on the pairwise incompatibility matrix,
not on the ambient polymer type. -/
theorem ursell_eq_of_incomp
    {P Q : PolymerSystem} {n : ℕ}
    (X : Fin n → P.Polymer) (Y : Fin n → Q.Polymer)
    (hinc : ∀ i j, P.incomp (X i) (X j) ↔
      Q.incomp (Y i) (Y j)) :
    ursell P X = ursell Q Y := by
  have hg : incompGraph P X = incompGraph Q Y := by
    ext i j
    rw [incompGraph_adj, incompGraph_adj]
    exact and_congr_right fun _ => hinc i j
  unfold ursell
  rw [hg]

/-- An exact equivalence of finite polymer systems: activities and pairwise
incompatibility are preserved. -/
structure PolymerSystemEquiv (P Q : PolymerSystem) where
  toEquiv : P.Polymer ≃ Q.Polymer
  incomp_iff : ∀ c c', P.incomp c c' ↔
    Q.incomp (toEquiv c) (toEquiv c')
  activity_eq : ∀ c, P.activity c = Q.activity (toEquiv c)

open Classical in
/-- Exact polymer-system equivalence preserves the entire cluster sum.  The
proof reindexes every finite tuple sum and then the outer `tsum`; no
convergence estimate or compactness argument is involved. -/
theorem clusterSum_eq_of_equiv
    {P Q : PolymerSystem} [Fintype P.Polymer] [Fintype Q.Polymer]
    (e : PolymerSystemEquiv P Q) :
    clusterSum P = clusterSum Q := by
  unfold clusterSum
  refine tsum_congr fun n => ?_
  congr 1
  let E : (Fin (n + 1) → P.Polymer) ≃
      (Fin (n + 1) → Q.Polymer) :=
    Equiv.piCongrRight (fun _ => e.toEquiv)
  refine Fintype.sum_equiv E _ _ ?_
  intro X
  have hu : ursell P X =
      ursell Q (fun i => e.toEquiv (X i)) := by
    apply ursell_eq_of_incomp
    exact fun i j => e.incomp_iff (X i) (X j)
  change (ursell P X : ℂ) * ∏ i, P.activity (X i) =
    (ursell Q (E X) : ℂ) * ∏ i, Q.activity (E X i)
  have hE : E X = fun i => e.toEquiv (X i) := rfl
  rw [hE]
  congr 1
  · exact congrArg (fun z : ℤ => (z : ℂ)) hu
  · exact Finset.prod_congr rfl fun i _ => e.activity_eq (X i)

end KP

namespace WindowPolymer

open Classical in
/-- Corresponding tuples of common-window polymers have the same Ursell
coefficient in every two fitting volumes. -/
theorem ursell_toWeightedPolymer_eq
    {d N M n : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (wN : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (wM : GaugeConfig d M G → ConcretePlaquette d M → ℝ)
    (X : Fin n → WindowPolymer d)
    (hN : ∀ i, (X i).Fits N) (hM : ∀ i, (X i).Fits M) :
    KP.ursell
      (weightedLatticePolymerSystem (d := d) (N := N) μ wN)
      (fun i => (X i).toWeightedPolymer μ wN (hN i))
      =
    KP.ursell
      (weightedLatticePolymerSystem (d := d) (N := M) μ wM)
      (fun i => (X i).toWeightedPolymer μ wM (hM i)) := by
  apply KP.ursell_eq_of_incomp
  intro i j
  rw [(X i).incomp_toWeightedPolymer_iff μ wN (X j)
      (hN i) (hN j),
    (X i).incomp_toWeightedPolymer_iff μ wM (X j)
      (hM i) (hM j)]

open Classical in
/-- Corresponding tuples of common-window polymers form a cluster in one
fitting volume exactly when they form a cluster in any other. -/
theorem isCluster_toWeightedPolymer_iff
    {d N M n : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (wN : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (wM : GaugeConfig d M G → ConcretePlaquette d M → ℝ)
    (X : Fin n → WindowPolymer d)
    (hN : ∀ i, (X i).Fits N) (hM : ∀ i, (X i).Fits M) :
    KP.IsCluster
        (weightedLatticePolymerSystem (d := d) (N := N) μ wN)
        (fun i => (X i).toWeightedPolymer μ wN (hN i))
      ↔
    KP.IsCluster
        (weightedLatticePolymerSystem (d := d) (N := M) μ wM)
        (fun i => (X i).toWeightedPolymer μ wM (hM i)) := by
  unfold KP.IsCluster
  have hg :
      KP.incompGraph
          (weightedLatticePolymerSystem (d := d) (N := N) μ wN)
          (fun i => (X i).toWeightedPolymer μ wN (hN i))
        =
      KP.incompGraph
          (weightedLatticePolymerSystem (d := d) (N := M) μ wM)
          (fun i => (X i).toWeightedPolymer μ wM (hM i)) := by
    ext i j
    rw [KP.incompGraph_adj, KP.incompGraph_adj]
    refine and_congr_right fun _ => ?_
    rw [(X i).incomp_toWeightedPolymer_iff μ wN (X j)
        (hN i) (hN j),
      (X i).incomp_toWeightedPolymer_iff μ wM (X j)
        (hM i) (hM j)]
  rw [hg]

open Classical in
/-- The complete cluster monomial (Ursell coefficient times activities) of a
common-window tuple is identical in two fitting tori. -/
theorem clusterMonomial_toWeightedPolymer_eq
    {d N M n : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (X : Fin n → WindowPolymer d)
    (hN : ∀ i, (X i).Fits N) (hM : ∀ i, (X i).Fits M) :
    (KP.ursell
      (weightedLatticePolymerSystem (d := d) (N := N) μ
        (fun (A : GaugeConfig d N G) (p : ConcretePlaquette d N) =>
          plaquetteWeight pe β A p))
      (fun i => (X i).toWeightedPolymer μ
        (N := N)
        (fun (A : GaugeConfig d N G) (p : ConcretePlaquette d N) =>
          plaquetteWeight pe β A p) (hN i)) : ℂ) *
      ∏ i, (weightedLatticePolymerSystem (d := d) (N := N) μ
        (fun (A : GaugeConfig d N G) (p : ConcretePlaquette d N) =>
          plaquetteWeight pe β A p)).activity
          ((X i).toWeightedPolymer μ
            (N := N)
            (fun (A : GaugeConfig d N G) (p : ConcretePlaquette d N) =>
              plaquetteWeight pe β A p) (hN i))
      =
    (KP.ursell
      (weightedLatticePolymerSystem (d := d) (N := M) μ
        (fun (A : GaugeConfig d M G) (p : ConcretePlaquette d M) =>
          plaquetteWeight pe β A p))
      (fun i => (X i).toWeightedPolymer μ
        (N := M)
        (fun (A : GaugeConfig d M G) (p : ConcretePlaquette d M) =>
          plaquetteWeight pe β A p) (hM i)) : ℂ) *
      ∏ i, (weightedLatticePolymerSystem (d := d) (N := M) μ
        (fun (A : GaugeConfig d M G) (p : ConcretePlaquette d M) =>
          plaquetteWeight pe β A p)).activity
          ((X i).toWeightedPolymer μ
            (N := M)
            (fun (A : GaugeConfig d M G) (p : ConcretePlaquette d M) =>
              plaquetteWeight pe β A p) (hM i)) := by
  congr 1
  · exact congrArg (fun z : ℤ => (z : ℂ))
      (ursell_toWeightedPolymer_eq μ
        (fun (A : GaugeConfig d N G) (p : ConcretePlaquette d N) =>
          plaquetteWeight pe β A p)
        (fun (A : GaugeConfig d M G) (p : ConcretePlaquette d M) =>
          plaquetteWeight pe β A p) X hN hM)
  · refine Finset.prod_congr rfl fun i _ => ?_
    exact (X i).activity_toWeightedPolymer_eq μ pe β (hN i) (hM i)

end WindowPolymer

end YangMills
