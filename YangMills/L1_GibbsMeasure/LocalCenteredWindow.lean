/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalCentering
import YangMills.L1_GibbsMeasure.LocalWindowCauchy
import YangMills.L1_GibbsMeasure.LocalCorrectionSeries

/-!
# Centered common windows for local cluster corrections

The positive translation word from `LocalCentering` moves an arbitrary
finite observable support away from the lower periodic seam.  A plaquette
incident to that support then has a bilateral margin, and every cluster
below a fixed cardinality cutoff can be decoded into the same common window
in two sufficiently large volumes.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace ConcreteSupport

open Classical

/-- Membership in the discarded local plaquette region is exactly incidence
with one positive edge of the pinning support. -/
theorem mem_supportPlaquettes_iff
    {d N : ℕ} [NeZero d] [NeZero N]
    {SF : Finset (PosEdge d N)} {p : ConcretePlaquette d N} :
    p ∈ supportPlaquettes SF ↔
      ∃ e ∈ SF, e ∈ plaquetteSupport p := by
  simp [supportPlaquettes, localFarRegion, farRegion,
    edgeSupport_supportEdgeList, Finset.not_disjoint_iff]

end ConcreteSupport

namespace CompatibleLocalObservable

open Classical

/-- Every realized edge of the centered observable has each source
coordinate between the shift radius and the shifted original support
bound. -/
theorem centered_realizedSupport_source_bounds
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (r : ℕ)
    (hC : (O.center r).minVolume ≤ n)
    {e : PosEdge d (n + 1)} (he : e ∈ (O.center r).realizedSupport n hC)
    (j : Fin d) :
    r ≤ (e.1.source j).val ∧
      (e.1.source j).val < O.minVolume + r + 1 := by
  rw [realizedSupport, Finset.mem_map] at he
  obtain ⟨s, -, rfl⟩ := he
  have hcoord :
      (((O.center r).coord s).1 j)
        =
      (O.coord
        (O.translateListSupportEquiv (centeringWord d r) s)).1 j + r :=
    O.coord_centeringWord_source r s j
  have horig :
      (O.coord
        (O.translateListSupportEquiv (centeringWord d r) s)).1 j
        < O.minVolume + 1 :=
    O.coord_lt _ j
  have hfit : ((O.center r).coord s).1 j < n + 1 :=
    lt_of_lt_of_le ((O.center r).coord_lt s j) (by omega)
  change
    r ≤ ((O.center r).coord s).1 j % (n + 1) ∧
      ((O.center r).coord s).1 j % (n + 1) <
        O.minVolume + r + 1
  rw [Nat.mod_eq_of_lt hfit]
  omega

/-- A plaquette meeting the centered observable support has lower margin
`R` and upper coordinate bounded by the shifted original support. -/
theorem supportPlaquette_centered_bounds
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    {p : ConcretePlaquette d (n + 1)}
    (hp : p ∈ supportPlaquettes
      ((O.center (R + 2)).realizedSupport n hC))
    (j : Fin d) :
    R < (p.site j).val ∧
      (p.site j).val < O.minVolume + (R + 2) + 1 := by
  obtain ⟨e, heS, hep⟩ :=
    ConcreteSupport.mem_supportPlaquettes_iff.mp hp
  have heB :=
    O.centered_realizedSupport_source_bounds (R + 2) hC heS j
  have hepos : 0 < (e.1.source j).val := by omega
  have hpB :=
    ConcretePlaquette.site_bounds_of_mem_plaquetteSupport
      p hep j hepos
  omega

/-- The centered support plaquette has a bilateral source-volume margin
whenever that volume has the stated explicit upper room. -/
theorem supportPlaquette_centered_siteMargin
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom : O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {p : ConcretePlaquette d (n + 1)}
    (hp : p ∈ supportPlaquettes
      ((O.center (R + 2)).realizedSupport n hC)) :
    p.SiteMargin R := by
  intro j
  have hpB := O.supportPlaquette_centered_bounds R hC hp j
  constructor <;> omega

/-- The same centered support plaquette has enough upper room to be decoded
in any second box satisfying the identical explicit size bound. -/
theorem supportPlaquette_centered_targetRoom
    {d n M : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (R : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hM : O.minVolume + (R + 2) + 1 + R + 1 < M)
    {p : ConcretePlaquette d (n + 1)}
    (hp : p ∈ supportPlaquettes
      ((O.center (R + 2)).realizedSupport n hC)) :
    ∀ j, (p.site j).val + R + 1 < M := by
  intro j
  have hpB := O.supportPlaquette_centered_bounds R hC hp j
  omega

end CompatibleLocalObservable

namespace WindowPolymer

open Classical

/-- Incidence with a finite common-window edge support is preserved and
reflected when the same fitting plaquette and edge set are realized in two
different volumes. -/
theorem WindowPlaquette.mem_supportPlaquettes_realizedFinset_iff
    {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
    (U : Finset (WindowPosEdge d))
    (uN : ∀ e ∈ U, e.Fits N)
    (uM : ∀ e ∈ U, e.Fits M)
    (p : WindowPlaquette d) (hpN : p.Fits N) (hpM : p.Fits M) :
    p.toConcrete hpN ∈
        supportPlaquettes (WindowPosEdge.realizedFinset U uN)
      ↔
    p.toConcrete hpM ∈
        supportPlaquettes (WindowPosEdge.realizedFinset U uM) := by
  constructor
  · intro hp
    obtain ⟨eN, heN, hepN⟩ :=
      ConcreteSupport.mem_supportPlaquettes_iff.mp hp
    obtain ⟨e, heRealN⟩ :=
      WindowPosEdge.mem_realizedFinset_iff.mp heN
    obtain ⟨k, hk⟩ :=
      WindowPlaquette.exists_posEdge_eq_of_mem_support p hpN hepN
    have heq : e.1 = p.posEdge k :=
      WindowPosEdge.eq_of_toPosEdge_eq
        (uN e.1 e.2) (p.posEdge_fits hpN k)
        (heRealN.trans hk)
    apply ConcreteSupport.mem_supportPlaquettes_iff.mpr
    refine ⟨e.1.toPosEdge (uM e.1 e.2), ?_, ?_⟩
    · apply WindowPosEdge.mem_realizedFinset_iff.mpr
      exact ⟨e, rfl⟩
    · simpa only [heq] using
        p.toConcrete_posEdge_mem_support hpM k
  · intro hp
    obtain ⟨eM, heM, hepM⟩ :=
      ConcreteSupport.mem_supportPlaquettes_iff.mp hp
    obtain ⟨e, heRealM⟩ :=
      WindowPosEdge.mem_realizedFinset_iff.mp heM
    obtain ⟨k, hk⟩ :=
      WindowPlaquette.exists_posEdge_eq_of_mem_support p hpM hepM
    have heq : e.1 = p.posEdge k :=
      WindowPosEdge.eq_of_toPosEdge_eq
        (uM e.1 e.2) (p.posEdge_fits hpM k)
        (heRealM.trans hk)
    apply ConcreteSupport.mem_supportPlaquettes_iff.mpr
    refine ⟨e.1.toPosEdge (uN e.1 e.2), ?_, ?_⟩
    · apply WindowPosEdge.mem_realizedFinset_iff.mpr
      exact ⟨e, rfl⟩
    · simpa only [heq] using
        p.toConcrete_posEdge_mem_support hpN k

/-- **Common-window realization of every centered below-cutoff cluster.**

If a cluster meets the centered observable support and has total plaquette
cardinality below `L`, it is the source realization of a single
volume-independent tuple which also fits in any second sufficiently large
box.  This is the exact geometric input for reindexing the finite
below-cutoff correction; no compactness or global configuration map is
used. -/
theorem exists_commonWindow_of_centered_smallCluster
    {d n m k : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hCn : (O.center (2 * L + 2)).minVolume ≤ n)
    (hroomN :
      O.minVolume + (2 * L + 2) + 1 + (2 * L) + 1 < n + 1)
    (hroomM :
      O.minVolume + (2 * L + 2) + 1 + (2 * L) + 1 < m + 1)
    {X : Fin k →
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β).Polymer}
    (hX : KP.IsCluster
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) X)
    (hmeet : ∃ i, ¬ Disjoint (X i).1
      (supportPlaquettes
        ((O.center (2 * L + 2)).realizedSupport n hCn)))
    (hsmall : (∑ i, (X i).1.card) < L) :
    ∃ Y : Fin k → WindowPolymer d,
      ∃ hYn : ∀ j, (Y j).Fits (n + 1),
      ∃ _hYm : ∀ j, (Y j).Fits (m + 1),
      ∀ j,
        (Y j).toWeightedPolymer μ
          (wilsonPlaquetteWeight pe β) (hYn j) = X j := by
  obtain ⟨i₀, hi₀⟩ := hmeet
  obtain ⟨p, hpX, hpS⟩ := Finset.not_disjoint_iff.mp hi₀
  have hpMarginLarge : p.SiteMargin (2 * L) :=
    O.supportPlaquette_centered_siteMargin
      (2 * L) hCn hroomN hpS
  have hcard : 2 * ∑ i, (X i).1.card ≤ 2 * L := by omega
  have hpMargin : p.SiteMargin (2 * ∑ i, (X i).1.card) :=
    hpMarginLarge.mono hcard
  let Y := decodedClusterTuple μ
    (wilsonPlaquetteWeight pe β) hX hpX hpMargin
  have hYn : ∀ j, (Y j).Fits (n + 1) :=
    decodedClusterTuple_fits_source μ
      (wilsonPlaquetteWeight pe β) hX hpX hpMargin
  have hpTargetLarge : ∀ j, (p.site j).val + (2 * L) + 1 < m + 1 :=
    O.supportPlaquette_centered_targetRoom
      (2 * L) hCn hroomM hpS
  have hpTarget :
      ∀ j, (p.site j).val + (2 * ∑ i, (X i).1.card) + 1 < m + 1 := by
    intro j
    have hj := hpTargetLarge j
    omega
  have hYm : ∀ j, (Y j).Fits (m + 1) :=
    decodedClusterTuple_fits_target μ
      (wilsonPlaquetteWeight pe β) hX hpX hpMargin hpTarget
  refine ⟨Y, hYn, hYm, ?_⟩
  intro j
  exact toWeightedPolymer_decodedClusterTuple μ
    (wilsonPlaquetteWeight pe β) hX hpX hpMargin j

end WindowPolymer

end YangMills
