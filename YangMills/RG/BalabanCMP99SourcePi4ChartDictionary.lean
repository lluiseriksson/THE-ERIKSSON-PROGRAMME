/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4RangeProtection
import YangMills.RG.BalabanCMP99LiteralPhysicalChartDictionary

/-!
# Literal CMP99 source charts from the `Pi^4` collar

On a small periodic torus two distinct source cells can have the same
Chebyshev radius-two collar.  Consequently the map

`cell |-> cmp99SourcePi4CollarDomain cell`

must not be declared injective.  This file uses the correct finite quotient:
the geometric chart is the collar domain itself, and its physical core is the
union of the base-cell cores of every centre that generates that collar.

The construction therefore retains the literal CMP99 factor label while
avoiding both a false collar-centre injectivity theorem and a branching factor
proportional to the ambient volume.  The already proved bilateral range
protection supplies core containment and the physical near-to-meeting
property required by `CMP99LabeledPhysicalChartDictionary`.
-/

namespace YangMills.RG

noncomputable section

universe u w

/-- The source-specific simple-domain type at the printed `Pi^4` size. -/
abbrev CMP99SourcePi4Domain (Q : ℕ) [NeZero Q] :=
  CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) 625

/-- Literal source chart: a CMP99 factor label paired with a geometric
`Pi^4` collar domain. -/
abbrev CMP99SourcePi4Chart (Label : Type u) (Q : ℕ) [NeZero Q] :=
  CMP99WalkStep Label (CMP99SourcePi4Domain Q)

/-- The finite image of source cells under the literal `Pi^4` collar map.
Repeated full collars on small tori occur only once. -/
noncomputable def cmp99SourcePi4Domains {Q : ℕ} [NeZero Q] :
    Finset (CMP99SourcePi4Domain Q) := by
  classical
  exact Finset.univ.image cmp99SourcePi4CollarDomain

@[simp] theorem mem_cmp99SourcePi4Domains_iff {Q : ℕ} [NeZero Q]
    (X : CMP99SourcePi4Domain Q) :
    X ∈ cmp99SourcePi4Domains ↔
      ∃ cell : FinBox 4 Q, cmp99SourcePi4CollarDomain cell = X := by
  classical
  simp [cmp99SourcePi4Domains]

/-- All literal factor labels paired with the distinct geometric `Pi^4`
collars. -/
noncomputable def cmp99SourcePi4Charts
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Q : ℕ} [NeZero Q] :
    Finset (CMP99SourcePi4Chart Label Q) := by
  classical
  exact (Finset.univ.product cmp99SourcePi4Domains).image fun pair =>
    ⟨pair.1, pair.2⟩

@[simp] theorem mem_cmp99SourcePi4Charts_iff
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Q : ℕ} [NeZero Q]
    (chart : CMP99SourcePi4Chart Label Q) :
    chart ∈ cmp99SourcePi4Charts ↔ chart.domain ∈ cmp99SourcePi4Domains := by
  classical
  constructor
  · intro hchart
    rw [cmp99SourcePi4Charts, Finset.mem_image] at hchart
    obtain ⟨pair, hpair, rfl⟩ := hchart
    exact (Finset.mem_product.mp hpair).2
  · intro hdomain
    rw [cmp99SourcePi4Charts, Finset.mem_image]
    refine ⟨(chart.label, chart.domain), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hdomain⟩
    · cases chart
      rfl

/-- Cells whose literal collar is the geometric domain of `chart`. -/
noncomputable def cmp99SourcePi4ChartCenters
    {Label : Type u} {Q : ℕ} [NeZero Q]
    (chart : CMP99SourcePi4Chart Label Q) : Finset (FinBox 4 Q) := by
  classical
  exact Finset.univ.filter fun cell =>
    cmp99SourcePi4CollarDomain cell = chart.domain

@[simp] theorem mem_cmp99SourcePi4ChartCenters_iff
    {Label : Type u} {Q : ℕ} [NeZero Q]
    (chart : CMP99SourcePi4Chart Label Q) (cell : FinBox 4 Q) :
    cell ∈ cmp99SourcePi4ChartCenters chart ↔
      cmp99SourcePi4CollarDomain cell = chart.domain := by
  classical
  simp [cmp99SourcePi4ChartCenters]

/-- Quotient-safe physical core: union all owner cores whose source cell has
the chart's collar. -/
noncomputable def cmp99SourcePi4ChartCore
    {Label : Type u} {M Q : ℕ} [NeZero M] [NeZero Q]
    (chart : CMP99SourcePi4Chart Label Q) :
    Finset (PhysicalBond 4 (M * (2 * Q))) :=
  (cmp99SourcePi4ChartCenters chart).biUnion
    (cmp99SourceBaseCellBondCore (M := M))

theorem mem_cmp99SourcePi4ChartCore_iff
    {Label : Type u} {M Q : ℕ} [NeZero M] [NeZero Q]
    (chart : CMP99SourcePi4Chart Label Q)
    (bond : PhysicalBond 4 (M * (2 * Q))) :
    bond ∈ cmp99SourcePi4ChartCore chart ↔
      ∃ cell : FinBox 4 Q,
        cmp99SourcePi4CollarDomain cell = chart.domain ∧
          bond ∈ cmp99SourceBaseCellBondCore (M := M) cell := by
  classical
  simp [cmp99SourcePi4ChartCore]

/-- Enlarged chart support is literally the bilateral physical support of its
geometric `Pi^4` collar. -/
noncomputable def cmp99SourcePi4ChartEnlarged
    {Label : Type u} {M Q : ℕ} [NeZero M] [NeZero Q]
    (chart : CMP99SourcePi4Chart Label Q) :
    Finset (PhysicalBond 4 (M * (2 * Q))) :=
  cmp99SourceDomainPhysicalBondSupport chart.domain

/-- Every quotient core lies in the literal bilateral collar support. -/
theorem cmp99SourcePi4ChartCore_subset_enlarged
    {Label : Type u} {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (hrange : Rrange + 1 ≤ 4 * M)
    (chart : CMP99SourcePi4Chart Label Q) :
    cmp99SourcePi4ChartCore (M := M) chart ⊆
      cmp99SourcePi4ChartEnlarged chart := by
  intro bond hbond
  rw [mem_cmp99SourcePi4ChartCore_iff] at hbond
  obtain ⟨cell, hcell, hbond⟩ := hbond
  rw [cmp99SourcePi4ChartEnlarged, ← hcell]
  exact cmp99SourceBaseCellBondCore_subset_pi4PhysicalSupport
    cell hrange hbond

/-- The entire interaction-range neighbourhood of a quotient-core bond stays
inside the same literal `Pi^4` collar. -/
theorem cmp99SourcePi4ChartCore_rangeProtected
    {Label : Type u} {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (hrange : Rrange + 1 ≤ 4 * M)
    (chart : CMP99SourcePi4Chart Label Q)
    (source : PhysicalBond 4 (M * (2 * Q)))
    (hsource : source ∈ cmp99SourcePi4ChartCore chart)
    (target : PhysicalBond 4 (M * (2 * Q)))
    (hdist : physicalBondDist source target ≤ Rrange) :
    target ∈ cmp99SourcePi4ChartEnlarged chart := by
  rw [mem_cmp99SourcePi4ChartCore_iff] at hsource
  obtain ⟨cell, hcell, hsource⟩ := hsource
  rw [cmp99SourcePi4ChartEnlarged, ← hcell]
  exact mem_cmp99SourcePi4CollarDomain_physicalBondSupport_of_range
    cell source target hsource hdist hrange

/-- A physically surviving transition between quotient-safe source charts
forces their literal collar domains to meet. -/
theorem cmp99SourcePi4ChartCanFollow_implies_domainsMeet
    {Label : Type u} {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (hrange : Rrange + 1 ≤ 4 * M)
    (left right : CMP99SourcePi4Chart Label Q)
    (hfollow : CMP99PhysicalPatchCanFollow
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist Rrange left right) :
    left.domain.Meets right.domain := by
  classical
  rw [CMP99PhysicalPatchCanFollow, CMP99PhysicalRangeSeparated] at hfollow
  push_neg at hfollow
  obtain ⟨source, hsource, target, htarget, hdist⟩ := hfollow
  exact cmp99SourceDomains_meet_of_commonPhysicalBond
    (cmp99SourcePi4ChartCore_rangeProtected hrange left source hsource
      target hdist)
    htarget

set_option maxHeartbeats 800000 in
/-- Complete source-specific labelled chart dictionary.  Coincident collars
on small tori are quotient-merged geometrically, while all owner cores are
retained in their union. -/
noncomputable def cmp99SourcePi4PhysicalChartDictionary
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M Q T Rrange : ℕ} [NeZero M] [NeZero Q]
    (blockActive : FinBox 4 Q → Finset Cube)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (hrange : Rrange + 1 ≤ 4 * M) :
    CMP99LabeledPhysicalChartDictionary
      (ι := CMP99SourcePi4Chart Label Q)
      (Label := Label) (V := FinBox 4 Q) (Cube := Cube)
      (d := 4) (N := M * (2 * Q))
      (cmp116CoarseFaceAdj 4 Q) 625 (T * 625)
      physicalBondDist Rrange where
  charts := cmp99SourcePi4Charts
  core := cmp99SourcePi4ChartCore
  enlarged := cmp99SourcePi4ChartEnlarged
  factorLabel := fun chart => chart.1.label
  domainOf := fun chart => chart.1.domain
  domainActive := fun chart =>
    cmp99SimpleDomainActive blockActive chart.1.domain
  core_subset_enlarged := fun chart _ =>
    cmp99SourcePi4ChartCore_subset_enlarged hrange chart
  labeledDomain_injective := by
    rintro ⟨⟨leftLabel, leftDomain⟩, hleft⟩
      ⟨⟨rightLabel, rightDomain⟩, hright⟩ hEq
    change (leftLabel, leftDomain) = (rightLabel, rightDomain) at hEq
    cases hEq
    rfl
  near_implies_meets := fun left right hfollow =>
    cmp99SourcePi4ChartCanFollow_implies_domainsMeet
      (Label := Label) (M := M) (Q := Q) (Rrange := Rrange)
      hrange left.1 right.1 hfollow
  active_card_le := fun chart =>
    card_cmp99SimpleDomainActive_le blockActive T hT chart.1.domain

@[simp] theorem cmp99SourcePi4PhysicalChartDictionary_charts
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M Q T Rrange : ℕ} [NeZero M] [NeZero Q]
    (blockActive : FinBox 4 Q → Finset Cube)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (hrange : Rrange + 1 ≤ 4 * M) :
    (cmp99SourcePi4PhysicalChartDictionary blockActive hT hrange).charts =
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Label Q)) :=
  rfl

@[simp] theorem cmp99SourcePi4PhysicalChartDictionary_core
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M Q T Rrange : ℕ} [NeZero M] [NeZero Q]
    (blockActive : FinBox 4 Q → Finset Cube)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (hrange : Rrange + 1 ≤ 4 * M)
    (chart : CMP99SourcePi4Chart Label Q) :
    (cmp99SourcePi4PhysicalChartDictionary blockActive hT hrange).core chart =
      cmp99SourcePi4ChartCore chart :=
  rfl

@[simp] theorem cmp99SourcePi4PhysicalChartDictionary_enlarged
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M Q T Rrange : ℕ} [NeZero M] [NeZero Q]
    (blockActive : FinBox 4 Q → Finset Cube)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (hrange : Rrange + 1 ≤ 4 * M)
    (chart : CMP99SourcePi4Chart Label Q) :
    (cmp99SourcePi4PhysicalChartDictionary blockActive hT hrange).enlarged chart =
      cmp99SourcePi4ChartEnlarged chart :=
  rfl

@[simp] theorem cmp99SourcePi4PhysicalChartDictionary_domainOf
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M Q T Rrange : ℕ} [NeZero M] [NeZero Q]
    (blockActive : FinBox 4 Q → Finset Cube)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (hrange : Rrange + 1 ≤ 4 * M)
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Label Q))) :
    (cmp99SourcePi4PhysicalChartDictionary blockActive hT hrange).domainOf
        chart = chart.1.domain :=
  rfl

@[simp] theorem cmp99SourcePi4PhysicalChartDictionary_domainActive
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M Q T Rrange : ℕ} [NeZero M] [NeZero Q]
    (blockActive : FinBox 4 Q → Finset Cube)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (hrange : Rrange + 1 ≤ 4 * M)
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Label Q))) :
    (cmp99SourcePi4PhysicalChartDictionary blockActive hT hrange).domainActive
        chart = cmp99SimpleDomainActive blockActive chart.1.domain :=
  rfl

end

end YangMills.RG
