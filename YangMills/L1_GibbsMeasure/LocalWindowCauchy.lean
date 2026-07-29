/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalWindowCluster

/-!
# Common-window decomposition for the local Gibbs Cauchy estimate

This module supplies the inverse direction of the common-window bridge.
A finite-volume polymer all of whose plaquettes avoid the periodic seam
decodes to a volume-independent `WindowPolymer`; realizing it again recovers
the original polymer exactly, including its cardinality.

This is the first bookkeeping brick in the boundary/Cauchy argument.  No
thermodynamic limit is asserted here.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- A cluster of the weighted connected lattice gas admits an actual touching
walk between any two of its plaquettes, with length at most twice the total
plaquette cardinality.  The proof transports the weight-independent walk
construction from `ClusterGeometry`; it records reachability, not merely a
numerical distance inequality. -/
theorem weighted_exists_touchWalk_le
    {d N n : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    {X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) X)
    {i₀ j₀ : Fin n} {p q : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1) (hq : q ∈ (X j₀).1) :
    ∃ W : (touchGraph d N).Walk p q,
      W.length ≤ 2 * ∑ i, (X i).1.card := by
  classical
  have hX' : KP.IsCluster
      (connectedLatticePolymerSystem (d := d) (N := N)
        μ (fun _ => (0 : ℝ)) 0) X := hX
  obtain ⟨v⟩ := hX'.preconnected i₀ j₀
  obtain ⟨W, hW⟩ := exists_walk_through_cluster
    μ (fun _ => (0 : ℝ)) 0 v.bypass
      (SimpleGraph.Walk.bypass_isPath v) p hp q hq
  refine ⟨W, le_trans hW ?_⟩
  have hsupport :
      ∑ i ∈ v.bypass.support.toFinset, (X i).1.card
        ≤ ∑ i, (X i).1.card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hlength : v.bypass.length < n := by
    have h := (SimpleGraph.Walk.bypass_isPath v).length_lt
    rwa [Fintype.card_fin] at h
  have hn : n ≤ ∑ i, (X i).1.card := by
    calc
      n = ∑ _i : Fin n, 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one,
          Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ i, (X i).1.card :=
        Finset.sum_le_sum fun i _ =>
          Finset.card_pos.mpr (X i).2.1
  omega

/-- If one plaquette of a cluster has margin twice the cluster's total
cardinality, then every plaquette in every polymer of the cluster avoids the
periodic seam. -/
theorem cluster_siteMargin_zero
    {d N n : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    {X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) X)
    {i₀ : Fin n} {p : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1)
    (hmargin : p.SiteMargin (2 * ∑ i, (X i).1.card)) :
    ∀ j q, q ∈ (X j).1 → q.SiteMargin 0 := by
  intro j q hq
  obtain ⟨W, hW⟩ :=
    weighted_exists_touchWalk_le μ w hX hp hq
  have hpW : p.SiteMargin W.length :=
    hmargin.mono hW
  exact ConcretePlaquette.siteMargin_of_touchWalk W
    (by simpa using hpW)

/-- Decode the support of a seam-avoiding finite-volume polymer to ordinary
natural-number coordinates. -/
noncomputable def decodedSupport
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer) :
    Finset (WindowPlaquette d) :=
  c.1.image ConcretePlaquette.toWindow

/-- Every decoded plaquette fits back into the same volume when the original
polymer avoids the seam. -/
theorem decodedSupport_fits
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hmargin : ∀ p ∈ c.1, p.SiteMargin 0) :
    ∀ q ∈ decodedSupport μ w c, q.Fits N := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact ConcretePlaquette.toWindow_fits (hmargin p hp)

/-- Decoding a seam-avoiding polymer and realizing the decoded support gives
the original finite-volume support literally. -/
theorem realizedFinset_decodedSupport
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hmargin : ∀ p ∈ c.1, p.SiteMargin 0) :
    WindowPlaquette.realizedFinset (decodedSupport μ w c)
        (decodedSupport_fits μ w c hmargin) = c.1 := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hpq⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hq
    obtain ⟨r, hrc, hr⟩ := Finset.mem_image.mp p.2
    have hrm := hmargin r hrc
    have hre := ConcretePlaquette.toConcrete_toWindow hrm
    have hpr : p.1.toConcrete
        (decodedSupport_fits μ w c hmargin p.1 p.2) = r := by
      simpa [hr] using hre
    rw [hpr] at hpq
    simpa [hpq] using hrc
  · intro hq
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    let p : ↥(decodedSupport μ w c) :=
      ⟨q.toWindow, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    refine ⟨p, ?_⟩
    exact ConcretePlaquette.toConcrete_toWindow (hmargin q hq)

/-- Decode a seam-avoiding connected finite-volume polymer to the
volume-independent common window. -/
noncomputable def ofWeightedPolymer
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hmargin : ∀ p ∈ c.1, p.SiteMargin 0) :
    WindowPolymer d where
  support := decodedSupport μ w c
  nonempty := c.2.1.image ConcretePlaquette.toWindow
  connected := by
    apply (WindowPlaquette.isConnectedPolymer_realizedFinset_iff
      (decodedSupport μ w c)
      (decodedSupport_fits μ w c hmargin)).mpr
    simpa [realizedFinset_decodedSupport μ w c hmargin] using c.2.2

@[simp]
theorem ofWeightedPolymer_support
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hmargin : ∀ p ∈ c.1, p.SiteMargin 0) :
    (ofWeightedPolymer μ w c hmargin).support =
      decodedSupport μ w c := rfl

/-- The decoded polymer fits in its source volume. -/
theorem ofWeightedPolymer_fits
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hmargin : ∀ p ∈ c.1, p.SiteMargin 0) :
    (ofWeightedPolymer μ w c hmargin).Fits N :=
  decodedSupport_fits μ w c hmargin

/-- Decoding and then realizing a seam-avoiding polymer is an exact left
inverse, not merely an equality of activities. -/
theorem toWeightedPolymer_ofWeightedPolymer
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hmargin : ∀ p ∈ c.1, p.SiteMargin 0) :
    (ofWeightedPolymer μ w c hmargin).toWeightedPolymer μ w
        (ofWeightedPolymer_fits μ w c hmargin) = c := by
  apply Subtype.ext
  exact realizedFinset_decodedSupport μ w c hmargin

/-- Seam-avoiding decoding preserves the polymer cardinality exactly. -/
theorem card_ofWeightedPolymer
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer)
    (hmargin : ∀ p ∈ c.1, p.SiteMargin 0) :
    (ofWeightedPolymer μ w c hmargin).support.card = c.1.card := by
  rw [← WindowPlaquette.card_realizedFinset
    (ofWeightedPolymer_fits μ w c hmargin)]
  exact congrArg Finset.card
    (realizedFinset_decodedSupport μ w c hmargin)

/-- Decode every polymer of a cluster whose marked plaquette has sufficient
margin. -/
noncomputable def decodedClusterTuple
    {d N n : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    {X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) X)
    {i₀ : Fin n} {p : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1)
    (hmargin : p.SiteMargin (2 * ∑ i, (X i).1.card)) :
    Fin n → WindowPolymer d :=
  fun j => ofWeightedPolymer μ w (X j)
    (cluster_siteMargin_zero μ w hX hp hmargin j)

/-- Every decoded cluster polymer fits in the source volume. -/
theorem decodedClusterTuple_fits_source
    {d N n : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    {X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) X)
    {i₀ : Fin n} {p : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1)
    (hmargin : p.SiteMargin (2 * ∑ i, (X i).1.card)) :
    ∀ j, (decodedClusterTuple μ w hX hp hmargin j).Fits N := by
  intro j
  exact ofWeightedPolymer_fits μ w (X j)
    (cluster_siteMargin_zero μ w hX hp hmargin j)

/-- Realizing the decoded tuple in the source volume recovers the original
tuple pointwise. -/
theorem toWeightedPolymer_decodedClusterTuple
    {d N n : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    {X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) X)
    {i₀ : Fin n} {p : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1)
    (hmargin : p.SiteMargin (2 * ∑ i, (X i).1.card))
    (j : Fin n) :
    (decodedClusterTuple μ w hX hp hmargin j).toWeightedPolymer μ w
        (decodedClusterTuple_fits_source μ w hX hp hmargin j) =
      X j := by
  exact toWeightedPolymer_ofWeightedPolymer μ w (X j)
    (cluster_siteMargin_zero μ w hX hp hmargin j)

/-- Decoding preserves each polymer size and therefore the total cluster
size used by the KP tail. -/
theorem sum_card_decodedClusterTuple
    {d N n : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    {X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := N) μ w) X)
    {i₀ : Fin n} {p : ConcretePlaquette d N}
    (hp : p ∈ (X i₀).1)
    (hmargin : p.SiteMargin (2 * ∑ i, (X i).1.card)) :
    ∑ i, (decodedClusterTuple μ w hX hp hmargin i).support.card =
      ∑ i, (X i).1.card := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact card_ofWeightedPolymer μ w (X i)
    (cluster_siteMargin_zero μ w hX hp hmargin i)

/-- The complete Ursell/activity monomial of a tuple in a weighted lattice
polymer system. -/
noncomputable def weightedClusterMonomial
    {d N n : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ w).Polymer) : ℂ :=
  (KP.ursell
    (weightedLatticePolymerSystem (d := d) (N := N) μ w) X : ℂ) *
    ∏ i, (weightedLatticePolymerSystem
      (d := d) (N := N) μ w).activity (X i)

/-- Wilson's single-plaquette weight, with the volume exposed as an
argument.  Naming it keeps later dependent types small enough for the
elaborator to reduce predictably. -/
noncomputable def wilsonPlaquetteWeight
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G]
    (pe : G → ℝ) (β : ℝ) :
    GaugeConfig d N G → ConcretePlaquette d N → ℝ :=
  fun (A : GaugeConfig d N G) (q : ConcretePlaquette d N) =>
    plaquetteWeight (d := d) (N := N) (G := G) pe β A q

/-- If a finite-volume tuple is the source realization of a common-window
tuple, its complete Ursell/activity monomial is exactly the monomial of the
same tuple realized in any second fitting volume.

For a seam-avoiding source cluster, instantiate `Y` with
`decodedClusterTuple`; `decodedClusterTuple_fits_source` supplies `hN` and
`toWeightedPolymer_decodedClusterTuple` supplies `hsource`. -/
theorem weightedClusterMonomial_eq_of_commonWindow
    {d N M n : ℕ} [NeZero d] [NeZero N] [NeZero M]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (X : Fin n →
      (weightedLatticePolymerSystem (d := d) (N := N) μ
        (wilsonPlaquetteWeight pe β)).Polymer)
    (Y : Fin n → WindowPolymer d)
    (hN : ∀ j, (Y j).Fits N)
    (hM : ∀ j, (Y j).Fits M)
    (hsource : ∀ j,
      (Y j).toWeightedPolymer μ (wilsonPlaquetteWeight pe β) (hN j) =
        X j) :
    weightedClusterMonomial μ (wilsonPlaquetteWeight pe β) X =
      weightedClusterMonomial μ (wilsonPlaquetteWeight pe β)
        (fun j => (Y j).toWeightedPolymer μ
          (wilsonPlaquetteWeight pe β) (hM j)) := by
  have htuple :
      (fun j => (Y j).toWeightedPolymer μ
        (wilsonPlaquetteWeight pe β) (hN j)) = X :=
    funext hsource
  rw [← htuple]
  exact clusterMonomial_toWeightedPolymer_eq μ pe β Y hN hM

end WindowPolymer

end YangMills
