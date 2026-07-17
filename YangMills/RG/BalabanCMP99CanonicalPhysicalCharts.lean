/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalChartCollarGeometry

/-!
# Canonical range-interior physical CMP99 charts

For a literal simple localization domain `X`, define its enlarged physical
carrier to be the full bond support of `X`.  Define its core to be the maximal
range-`R` interior: a supported bond belongs to the core exactly when every
bond within interaction range `R` is still supported by `X`.

These definitions generate all collar obligations used by the labelled chart
dictionary.  Thus a finite family of literal source steps `(alpha, X)` and a
block-to-weakening-cube incidence map now produce the complete physical chart
dictionary without independent injectivity, nesting, near-to-meeting, or
whole-domain active-cardinality binders.

Honest scope: this canonical maximal interior is a valid collar realization.
Identifying it with the particular CMP99 chart cover, proving that its cores
partition the physical bonds read by the patched parametrix, and fixing the
printed scale-dependent collar width remain separate source obligations.
-/

namespace YangMills.RG

noncomputable section

universe u w

/-- Full physical bond carrier of a literal CMP99 localization domain. -/
noncomputable def cmp99CanonicalChartEnlarged
    {Label : Type u} {M N' S : ℕ} [NeZero M] [NeZero N']
    (chart : CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)) :
    Finset (PhysicalBond 4 (M * N')) :=
  cmp99SimpleDomainPhysicalBondSupport chart.domain

/-- Maximal bond core whose closed range-`R` neighbourhood remains inside the
chart domain. -/
noncomputable def cmp99CanonicalChartCore
    {Label : Type u} {M N' S : ℕ} [NeZero M] [NeZero N']
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (R : ℕ)
    (chart : CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)) :
    Finset (PhysicalBond 4 (M * N')) := by
  classical
  exact (cmp99CanonicalChartEnlarged chart).filter fun source =>
    ∀ target, dist source target ≤ R →
      target ∈ cmp99CanonicalChartEnlarged chart

theorem cmp99CanonicalChartCore_subset_enlarged
    {Label : Type u} {M N' S : ℕ} [NeZero M] [NeZero N']
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (R : ℕ)
    (chart : CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)) :
    cmp99CanonicalChartCore dist R chart ⊆
      cmp99CanonicalChartEnlarged chart := by
  classical
  intro source hsource
  exact (Finset.mem_filter.mp hsource).1

theorem cmp99CanonicalChartCore_rangeProtected
    {Label : Type u} {M N' S : ℕ} [NeZero M] [NeZero N']
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (R : ℕ) :
    CMP99LiteralChartCoreRangeProtected
      (cmp99CanonicalChartCore (Label := Label) (S := S) dist R) dist R := by
  classical
  intro chart source hsource target hdist
  exact (Finset.mem_filter.mp hsource).2 target hdist

/-- A finite family of literal source steps yields the complete labelled
physical chart dictionary through the canonical range-interior collar. -/
noncomputable def cmp99CanonicalPhysicalChartDictionary
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M N' S T R : ℕ} [NeZero M] [NeZero N']
    (charts : Finset (CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)))
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (blockActive : FinBox 4 N' → Finset Cube)
    (hT : ∀ block, (blockActive block).card ≤ T) :
    CMP99LabeledPhysicalChartDictionary
      (ι := CMP99WalkStep Label
        (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S))
      (Label := Label) (V := FinBox 4 N') (Cube := Cube)
      (d := 4) (N := M * N')
      (cmp116CoarseFaceAdj 4 N') S (T * S) dist R :=
  cmp99LiteralCMP116PhysicalChartDictionary charts
    (cmp99CanonicalChartCore dist R) cmp99CanonicalChartEnlarged
    dist blockActive
    (fun chart _ => cmp99CanonicalChartCore_subset_enlarged dist R chart)
    (cmp99CanonicalChartCore_rangeProtected
      (Label := Label) (S := S) dist R)
    (fun _ => fun _ h => h)
    hT

end

end YangMills.RG
