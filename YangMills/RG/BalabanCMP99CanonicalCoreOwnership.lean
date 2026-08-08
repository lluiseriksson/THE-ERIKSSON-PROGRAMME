/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99CanonicalPhysicalCharts
import YangMills.RG.BalabanCMP99PatchedParametrixCorePartition

/-!
# Canonical ownership refinement of overlapping CMP99 cores

Literal CMP99 charts may have overlapping protected cores, and distinct factor
labels may use the same geometric localization domain.  Such overlap should
not be hidden by a false injectivity or disjointness premise.

This file isolates the one source-facing obligation that is actually needed:
the candidate cores cover every physical bond.  From that cover it chooses one
covering chart for each bond and refines every candidate core to its owned
subcore.  The owned subcores

* form an exact `CMP99PhysicalCorePartition`;
* remain subsets of the original protected cores; and therefore
* inherit every collar/range-protection statement proved for those cores.

The choice is only a deterministic tie-break between already valid charts; it
does not manufacture coverage.  Proving that the literal CMP99 chart family
covers every physical bond remains the explicit source obligation.
-/

namespace YangMills.RG

noncomputable section

universe u w

/-- A finite family of candidate cores covers every physical bond. -/
def CMP99PhysicalCoreCover
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N)) : Prop :=
  ∀ source, ∃ chart, chart ∈ charts ∧ source ∈ candidateCore chart

/-- Select one chart whose candidate core contains the source bond. -/
noncomputable def cmp99PhysicalCoreOwner
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N))
    (hcover : CMP99PhysicalCoreCover charts candidateCore)
    (source : PhysicalBond d N) : ι :=
  Classical.choose (hcover source)

theorem cmp99PhysicalCoreOwner_mem_charts
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N))
    (hcover : CMP99PhysicalCoreCover charts candidateCore)
    (source : PhysicalBond d N) :
    cmp99PhysicalCoreOwner charts candidateCore hcover source ∈ charts :=
  (Classical.choose_spec (hcover source)).1

theorem source_mem_candidateCore_owner
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N))
    (hcover : CMP99PhysicalCoreCover charts candidateCore)
    (source : PhysicalBond d N) :
    source ∈ candidateCore
      (cmp99PhysicalCoreOwner charts candidateCore hcover source) :=
  (Classical.choose_spec (hcover source)).2

/-- The subcore owned by one chart after resolving all overlaps. -/
noncomputable def cmp99PhysicalOwnedCore
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N))
    (hcover : CMP99PhysicalCoreCover charts candidateCore)
    (chart : ι) : Finset (PhysicalBond d N) := by
  classical
  exact Finset.univ.filter fun source =>
    cmp99PhysicalCoreOwner charts candidateCore hcover source = chart

theorem mem_cmp99PhysicalOwnedCore_iff
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N))
    (hcover : CMP99PhysicalCoreCover charts candidateCore)
    (chart : ι) (source : PhysicalBond d N) :
    source ∈ cmp99PhysicalOwnedCore charts candidateCore hcover chart ↔
      cmp99PhysicalCoreOwner charts candidateCore hcover source = chart := by
  classical
  simp [cmp99PhysicalOwnedCore]

/-- Ownership only removes overlap; it never enlarges a candidate core. -/
theorem cmp99PhysicalOwnedCore_subset_candidateCore
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N))
    (hcover : CMP99PhysicalCoreCover charts candidateCore)
    (chart : ι) :
    cmp99PhysicalOwnedCore charts candidateCore hcover chart ⊆
      candidateCore chart := by
  intro source hsource
  rw [mem_cmp99PhysicalOwnedCore_iff] at hsource
  simpa [hsource] using
    source_mem_candidateCore_owner charts candidateCore hcover source

/-- The owned refinement is an exact physical core partition. -/
theorem cmp99PhysicalOwnedCore_corePartition
    {ι : Type u} [DecidableEq ι]
    {d N : ℕ} [NeZero N]
    (charts : Finset ι)
    (candidateCore : ι → Finset (PhysicalBond d N))
    (hcover : CMP99PhysicalCoreCover charts candidateCore) :
    CMP99PhysicalCorePartition charts
      (cmp99PhysicalOwnedCore charts candidateCore hcover) := by
  intro source
  refine ⟨cmp99PhysicalCoreOwner charts candidateCore hcover source,
    cmp99PhysicalCoreOwner_mem_charts charts candidateCore hcover source, ?_, ?_⟩
  · rw [mem_cmp99PhysicalOwnedCore_iff]
  · intro chart hchart hsource
    rw [mem_cmp99PhysicalOwnedCore_iff] at hsource
    exact hsource.symm

/-- Owned canonical cores inherit the literal range protection of the maximal
range-interior cores. -/
theorem cmp99CanonicalOwnedCore_rangeProtected
    {Label : Type u} [DecidableEq Label]
    {M N' S : ℕ} [NeZero M] [NeZero N']
    (charts : Finset (CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)))
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (R : ℕ)
    (hcover : CMP99PhysicalCoreCover charts
      (cmp99CanonicalChartCore dist R)) :
    CMP99LiteralChartCoreRangeProtected
      (cmp99PhysicalOwnedCore charts
        (cmp99CanonicalChartCore dist R) hcover) dist R := by
  intro chart source hsource target hdist
  exact cmp99CanonicalChartCore_rangeProtected
    (Label := Label) (S := S) dist R chart source
      (cmp99PhysicalOwnedCore_subset_candidateCore charts
        (cmp99CanonicalChartCore dist R) hcover chart hsource)
      target hdist

/-- The canonical labelled chart dictionary with overlaps resolved by physical
core ownership.  Its sole additional geometric input is coverage by the
maximal range-interior candidate cores. -/
noncomputable def cmp99CanonicalOwnedPhysicalChartDictionary
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M N' S T R : ℕ} [NeZero M] [NeZero N']
    (charts : Finset (CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)))
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (blockActive : FinBox 4 N' → Finset Cube)
    (hcover : CMP99PhysicalCoreCover charts
      (cmp99CanonicalChartCore dist R))
    (hT : ∀ block, (blockActive block).card ≤ T) :
    CMP99LabeledPhysicalChartDictionary
      (ι := CMP99WalkStep Label
        (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S))
      (Label := Label) (V := FinBox 4 N') (Cube := Cube)
      (d := 4) (N := M * N')
      (cmp116CoarseFaceAdj 4 N') S (T * S) dist R :=
  cmp99LiteralCMP116PhysicalChartDictionary charts
    (cmp99PhysicalOwnedCore charts
      (cmp99CanonicalChartCore dist R) hcover)
    cmp99CanonicalChartEnlarged dist blockActive
    (fun chart _ =>
      (cmp99PhysicalOwnedCore_subset_candidateCore charts
        (cmp99CanonicalChartCore dist R) hcover chart).trans
          (cmp99CanonicalChartCore_subset_enlarged dist R chart))
    (cmp99CanonicalOwnedCore_rangeProtected charts dist R hcover)
    (fun _ => fun _ h => h)
    hT

/-- The core stored in the owned canonical dictionary is already the exact
physical partition required by the patched-parametrix identity. -/
theorem cmp99CanonicalOwnedPhysicalChartDictionary_corePartition
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M N' S T R : ℕ} [NeZero M] [NeZero N']
    (charts : Finset (CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)))
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (blockActive : FinBox 4 N' → Finset Cube)
    (hcover : CMP99PhysicalCoreCover charts
      (cmp99CanonicalChartCore dist R))
    (hT : ∀ block, (blockActive block).card ≤ T) :
    CMP99PhysicalCorePartition charts
      (cmp99CanonicalOwnedPhysicalChartDictionary charts dist blockActive
        hcover hT).core := by
  simpa [cmp99CanonicalOwnedPhysicalChartDictionary] using
    (cmp99PhysicalOwnedCore_corePartition charts
      (cmp99CanonicalChartCore dist R) hcover)

end

end YangMills.RG
