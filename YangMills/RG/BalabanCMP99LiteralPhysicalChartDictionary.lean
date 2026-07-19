/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99LabeledPhysicalChartDictionary
import YangMills.RG.BalabanCMP99SimpleDomainActiveCarrier

/-!
# Literal CMP99 physical charts

A CMP99 generalized-walk continuation is literally a pair `(alpha, X)`, where
`alpha` identifies the operator factor and `X` is its simple localization
domain.  The label type must retain every source index not determined by the
geometry (in particular scale or operator species when these are independent).

This file uses `CMP99WalkStep` itself as the chart type.  Consequently the pair
`(factorLabel, domainOf)` is injective by construction.  The weakening carrier
is also constructed, not supplied: it is the union of the weakening cubes
incident to the blocks of `X`, and a per-block incidence bound `T` gives the
exact dictionary budget `T*S`.

The two remaining premises are deliberately geometric and source-facing:

* the bond core of every literal step lies in its enlarged collar;
* a surviving physical chart transition maps to meeting source domains.

No synthetic chart enumeration or post-hoc domain label is introduced.
-/

namespace YangMills.RG

noncomputable section

universe u v w

variable {Label : Type u} [Fintype Label] [DecidableEq Label]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {Cube : Type w} [DecidableEq Cube]
variable {d N : ℕ} [NeZero N]
variable {G : SimpleGraph V} {S T Rrange : ℕ}
variable {dist : PhysicalBond d N → PhysicalBond d N → ℕ}

/-- Construct the labelled physical dictionary directly from a finite family
of literal CMP99 steps `(alpha, X)`. -/
noncomputable def cmp99LiteralPhysicalChartDictionary
    (charts : Finset
      (CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S)))
    (core enlarged :
      CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S) →
        Finset (PhysicalBond d N))
    (blockActive : V → Finset Cube)
    (hsub : ∀ chart, chart ∈ charts → core chart ⊆ enlarged chart)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist Rrange left right →
        left.1.domain.Meets right.1.domain)
    (hT : ∀ block, (blockActive block).card ≤ T) :
    CMP99LabeledPhysicalChartDictionary
      (ι := CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S))
      (Label := Label) (V := V) (Cube := Cube) (d := d) (N := N)
      G S (T * S) dist Rrange where
  charts := charts
  core := core
  enlarged := enlarged
  factorLabel := fun chart => chart.1.label
  domainOf := fun chart => chart.1.domain
  domainActive := fun chart =>
    cmp99SimpleDomainActive blockActive chart.1.domain
  core_subset_enlarged := hsub
  labeledDomain_injective := by
    rintro ⟨⟨leftLabel, leftDomain⟩, hleft⟩
      ⟨⟨rightLabel, rightDomain⟩, hright⟩ hEq
    change (leftLabel, leftDomain) = (rightLabel, rightDomain) at hEq
    cases hEq
    rfl
  near_implies_meets := hnear
  active_card_le := fun chart =>
    card_cmp99SimpleDomainActive_le blockActive T hT chart.1.domain

@[simp]
theorem cmp99LiteralPhysicalChartDictionary_factorLabel
    (charts : Finset
      (CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S)))
    (core enlarged :
      CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S) →
        Finset (PhysicalBond d N))
    (blockActive : V → Finset Cube)
    (hsub : ∀ chart, chart ∈ charts → core chart ⊆ enlarged chart)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist Rrange left right →
        left.1.domain.Meets right.1.domain)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (chart : ↥charts) :
    (cmp99LiteralPhysicalChartDictionary charts core enlarged blockActive
      hsub hnear hT).factorLabel chart = chart.1.label :=
  rfl

@[simp]
theorem cmp99LiteralPhysicalChartDictionary_domainOf
    (charts : Finset
      (CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S)))
    (core enlarged :
      CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S) →
        Finset (PhysicalBond d N))
    (blockActive : V → Finset Cube)
    (hsub : ∀ chart, chart ∈ charts → core chart ⊆ enlarged chart)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist Rrange left right →
        left.1.domain.Meets right.1.domain)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (chart : ↥charts) :
    (cmp99LiteralPhysicalChartDictionary charts core enlarged blockActive
      hsub hnear hT).domainOf chart = chart.1.domain :=
  rfl

@[simp]
theorem cmp99LiteralPhysicalChartDictionary_domainActive
    (charts : Finset
      (CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S)))
    (core enlarged :
      CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S) →
        Finset (PhysicalBond d N))
    (blockActive : V → Finset Cube)
    (hsub : ∀ chart, chart ∈ charts → core chart ⊆ enlarged chart)
    (hnear : ∀ (left right : ↥charts),
      CMP99PhysicalPatchCanFollow core enlarged dist Rrange left right →
        left.1.domain.Meets right.1.domain)
    (hT : ∀ block, (blockActive block).card ≤ T)
    (chart : ↥charts) :
    (cmp99LiteralPhysicalChartDictionary charts core enlarged blockActive
      hsub hnear hT).domainActive chart =
        cmp99SimpleDomainActive blockActive chart.1.domain :=
  rfl

end

end YangMills.RG
