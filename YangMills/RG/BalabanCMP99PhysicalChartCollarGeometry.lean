/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99LiteralPhysicalChartDictionary
import YangMills.RG.BalabanCMP116Eq219SourceGeometry

/-!
# Physical collar geometry for literal CMP99 charts

For the face-connected `M`-block domains used in CMP116, the physical bond
support is literal: both endpoint blocks of a bond belong to the domain.

This file replaces the abstract implication

`physical chart can follow -> source domains meet`

by the two collar statements that actually imply it:

* the `R`-neighbourhood of every core bond remains in its source domain;
* every enlarged-chart bond remains in its source domain.

A non-range-separated transition then supplies one bond in both physical
domain supports.  Its source block witnesses nonempty intersection of the two
simple localization domains.  Constructing the source collar with these two
properties remains the explicit downstream geometric task.
-/

namespace YangMills.RG

noncomputable section

universe u w

/-- Regard a CMP99 simple domain on the physical coarse-face graph as the
corresponding CMP116 localization domain. -/
def cmp99SimpleDomainToCMP116LocalizationDomain
    {M N' S : ℕ} [NeZero N']
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S) :
    CMP116LocalizationDomain M N' where
  blocks := X.blocks
  nonempty := X.nonempty
  connected := X.connected

/-- Literal physical bonds supported by a CMP99 simple localization domain. -/
noncomputable def cmp99SimpleDomainPhysicalBondSupport
    {M N' S : ℕ} [NeZero M] [NeZero N']
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S) :
    Finset (PhysicalBond 4 (M * N')) :=
  (cmp99SimpleDomainToCMP116LocalizationDomain (M := M) X).bondSupport

theorem mem_cmp99SimpleDomainPhysicalBondSupport_sourceBlock
    {M N' S : ℕ} [NeZero M] [NeZero N']
    {X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S}
    {bond : PhysicalBond 4 (M * N')}
    (hbond : bond ∈ cmp99SimpleDomainPhysicalBondSupport X) :
    cmp116BondSourceBlock bond ∈ X.blocks :=
  mem_cmp116LocalizationDomain_bondSupport_sourceBlock hbond

/-- A common physical bond forces the underlying coarse-block domains to
meet. -/
theorem cmp99SimpleDomains_meet_of_commonPhysicalBond
    {M N' S : ℕ} [NeZero M] [NeZero N']
    {X Y : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S}
    {bond : PhysicalBond 4 (M * N')}
    (hX : bond ∈ cmp99SimpleDomainPhysicalBondSupport X)
    (hY : bond ∈ cmp99SimpleDomainPhysicalBondSupport Y) :
    X.Meets Y := by
  rw [CMP99SimpleLocalizationDomain.Meets, Finset.not_disjoint_iff]
  exact ⟨cmp116BondSourceBlock bond,
    mem_cmp99SimpleDomainPhysicalBondSupport_sourceBlock hX,
    mem_cmp99SimpleDomainPhysicalBondSupport_sourceBlock hY⟩

/-- Exact source collar condition: every bond within interaction range of a
core bond remains supported by that chart's simple domain. -/
def CMP99LiteralChartCoreRangeProtected
    {Label : Type u} {M N' S : ℕ} [NeZero M] [NeZero N']
    (core : CMP99WalkStep Label
        (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S) →
      Finset (PhysicalBond 4 (M * N')))
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (R : ℕ) : Prop :=
  ∀ chart source, source ∈ core chart → ∀ target,
    dist source target ≤ R →
      target ∈ cmp99SimpleDomainPhysicalBondSupport chart.domain

/-- Protected cores and domain-supported enlargements produce the literal
source overlap condition for every physically surviving transition. -/
theorem cmp99PhysicalPatchCanFollow_implies_literalDomainsMeet
    {Label : Type u} {M N' S R : ℕ} [NeZero M] [NeZero N']
    (core enlarged : CMP99WalkStep Label
        (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S) →
      Finset (PhysicalBond 4 (M * N')))
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (hprotected : CMP99LiteralChartCoreRangeProtected core dist R)
    (henlarged : ∀ chart, enlarged chart ⊆
      cmp99SimpleDomainPhysicalBondSupport chart.domain)
    (left right : CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S))
    (hfollow : CMP99PhysicalPatchCanFollow core enlarged dist R left right) :
    left.domain.Meets right.domain := by
  classical
  rw [CMP99PhysicalPatchCanFollow, CMP99PhysicalRangeSeparated] at hfollow
  push_neg at hfollow
  obtain ⟨source, hsource, target, htarget, hdist⟩ := hfollow
  exact cmp99SimpleDomains_meet_of_commonPhysicalBond
    (hprotected left source hsource target hdist)
    (henlarged right htarget)

/-- Source-facing literal dictionary in which near-to-meeting is generated
from explicit collar protection rather than supplied as an independent
premise. -/
noncomputable def cmp99LiteralCMP116PhysicalChartDictionary
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {Cube : Type w} [DecidableEq Cube]
    {M N' S T R : ℕ} [NeZero M] [NeZero N']
    (charts : Finset (CMP99WalkStep Label
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S)))
    (core enlarged : CMP99WalkStep Label
        (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S) →
      Finset (PhysicalBond 4 (M * N')))
    (dist : PhysicalBond 4 (M * N') → PhysicalBond 4 (M * N') → ℕ)
    (blockActive : FinBox 4 N' → Finset Cube)
    (hsub : ∀ chart, chart ∈ charts → core chart ⊆ enlarged chart)
    (hprotected : CMP99LiteralChartCoreRangeProtected core dist R)
    (henlarged : ∀ chart, enlarged chart ⊆
      cmp99SimpleDomainPhysicalBondSupport chart.domain)
    (hT : ∀ block, (blockActive block).card ≤ T) :
    CMP99LabeledPhysicalChartDictionary
      (ι := CMP99WalkStep Label
        (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 N') S))
      (Label := Label) (V := FinBox 4 N') (Cube := Cube)
      (d := 4) (N := M * N')
      (cmp116CoarseFaceAdj 4 N') S (T * S) dist R :=
  cmp99LiteralPhysicalChartDictionary charts core enlarged blockActive hsub
    (fun left right hfollow =>
      cmp99PhysicalPatchCanFollow_implies_literalDomainsMeet
        core enlarged dist hprotected henlarged left right hfollow)
    hT

end

end YangMills.RG
