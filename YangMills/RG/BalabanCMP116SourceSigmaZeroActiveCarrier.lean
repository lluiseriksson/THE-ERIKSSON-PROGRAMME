/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4ChartDictionary

/-!
# The literal CMP116 `sigma_0` weakening carrier

CMP116 introduces a regular partition `sigma_0` into cubes of side `M`,
disjoint from the interior of the distinguished `Pi^4`.  In the periodic
source coordinates already used by the CMP99 chart construction, these cubes
are exactly the large blocks outside the large-block carrier of the
distinguished `Pi^4` collar.

This file constructs that family and the exact incidence map from a source
cell `Pi` to the weakening cubes which meet it.  A source cell contains
literally `2^4 = 16` large blocks, so the resulting physical `Pi^4` chart
activates at most `16 * 625 = 10000` weakening cubes.  More strongly, its
active carrier is proved equal to its large-block carrier intersected with
`sigma_0`; this is the source identity used in the weakening monomial, not
merely a cardinality majorant.

The CMP99 continuation label remains abstract on purpose.  Sect. C says that
`alpha` enumerates the several possible factors and gives a non-exhaustive
list followed by "etc."; inventing a closed inductive enumeration here would
not be source-faithful.
-/

namespace YangMills.RG

noncomputable section

universe u

/-- The literal regular weakening partition `sigma_0`: all side-`M` large
blocks outside the distinguished source `Pi^4` collar. -/
noncomputable def cmp116SourceSigmaZero {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q) : Finset (FinBox 4 (2 * Q)) :=
  Finset.univ \ cmp99SourceDomainLargeBlocks
    (cmp99SourcePi4CollarDomain anchor)

@[simp] theorem mem_cmp116SourceSigmaZero_iff {Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q) (block : FinBox 4 (2 * Q)) :
    block ∈ cmp116SourceSigmaZero anchor ↔
      cmp99SourceBaseCellOwner block ∉
        (cmp99SourcePi4CollarDomain anchor).blocks := by
  classical
  simp [cmp116SourceSigmaZero, mem_cmp99SourceDomainLargeBlocks_iff]

/-- Weakening cubes from `sigma_0` which meet one source base cell. -/
noncomputable def cmp116SourceSigmaZeroBlockActive
    {Q : ℕ} [NeZero Q] (anchor cell : FinBox 4 Q) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp99SourceBaseCell cell ∩ cmp116SourceSigmaZero anchor

@[simp] theorem mem_cmp116SourceSigmaZeroBlockActive_iff
    {Q : ℕ} [NeZero Q] (anchor cell : FinBox 4 Q)
    (block : FinBox 4 (2 * Q)) :
    block ∈ cmp116SourceSigmaZeroBlockActive anchor cell ↔
      cmp99SourceBaseCellOwner block = cell ∧
        cmp99SourceBaseCellOwner block ∉
          (cmp99SourcePi4CollarDomain anchor).blocks := by
  classical
  simp [cmp116SourceSigmaZeroBlockActive,
    mem_cmp99SourceBaseCell_iff]

/-- Each source cell meets at most its literal sixteen large blocks. -/
theorem card_cmp116SourceSigmaZeroBlockActive_le
    {Q : ℕ} [NeZero Q] (anchor cell : FinBox 4 Q) :
    (cmp116SourceSigmaZeroBlockActive anchor cell).card ≤ 16 := by
  calc
    (cmp116SourceSigmaZeroBlockActive anchor cell).card ≤
        (cmp99SourceBaseCell cell).card := by
      exact Finset.card_le_card Finset.inter_subset_left
    _ = 16 := card_cmp99SourceBaseCell cell

/-- The active weakening cubes of a source domain are exactly its literal
large-block carrier restricted to `sigma_0`. -/
theorem cmp99SimpleDomainActive_sourceSigmaZero
    {Q S : ℕ} [NeZero Q] (anchor : FinBox 4 Q)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    cmp99SimpleDomainActive
        (cmp116SourceSigmaZeroBlockActive anchor) X =
      cmp99SourceDomainLargeBlocks X ∩ cmp116SourceSigmaZero anchor := by
  classical
  ext block
  simp only [cmp99SimpleDomainActive, Finset.mem_biUnion,
    mem_cmp116SourceSigmaZeroBlockActive_iff, Finset.mem_inter,
    mem_cmp99SourceDomainLargeBlocks_iff, mem_cmp116SourceSigmaZero_iff]
  constructor
  · rintro ⟨cell, hcell, howner, hout⟩
    exact ⟨howner ▸ hcell, hout⟩
  · rintro ⟨howner, hout⟩
    exact ⟨cmp99SourceBaseCellOwner block, howner, rfl, hout⟩

set_option maxHeartbeats 800000 in
/-- The source-specific physical chart dictionary: literal `Pi^4` collars,
literal `sigma_0` incidence, and the fully explicit active budget `10000`. -/
noncomputable def cmp116SourceSigmaZeroPi4PhysicalChartDictionary
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (hrange : Rrange + 1 ≤ 4 * M) :
    CMP99LabeledPhysicalChartDictionary
      (ι := CMP99SourcePi4Chart Label Q)
      (Label := Label) (V := FinBox 4 Q)
      (Cube := FinBox 4 (2 * Q))
      (d := 4) (N := M * (2 * Q))
      (cmp116CoarseFaceAdj 4 Q) 625 10000
      physicalBondDist Rrange := by
  simpa using
    (cmp99SourcePi4PhysicalChartDictionary
      (Label := Label) (M := M) (Q := Q) (T := 16)
      (Rrange := Rrange)
      (cmp116SourceSigmaZeroBlockActive anchor)
      (card_cmp116SourceSigmaZeroBlockActive_le anchor) hrange)

@[simp] theorem cmp116SourceSigmaZeroPi4PhysicalChartDictionary_domainActive
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (hrange : Rrange + 1 ≤ 4 * M)
    (chart : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Label Q))) :
    (cmp116SourceSigmaZeroPi4PhysicalChartDictionary anchor hrange).domainActive
        chart =
      cmp99SourceDomainLargeBlocks chart.1.domain ∩
        cmp116SourceSigmaZero anchor := by
  change cmp99SimpleDomainActive
      (cmp116SourceSigmaZeroBlockActive anchor) chart.1.domain = _
  exact cmp99SimpleDomainActive_sourceSigmaZero anchor chart.1.domain

/-- The weakening carrier of a complete generalized walk is literally the
union of the `sigma_0`-restricted large-block carriers of all its source
domains. -/
theorem cmp116SourceSigmaZeroPi4PhysicalChartDictionary_walkActive
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (hrange : Rrange + 1 ≤ 4 * M)
    (walk : CMP99GeneralizedWalk Label
      ↥(cmp116SourceSigmaZeroPi4PhysicalChartDictionary
        (Label := Label) anchor hrange).charts) :
    walk.active
        (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
          (Label := Label) anchor hrange).domainActive =
      (walk.domains.map fun chart =>
        cmp99SourceDomainLargeBlocks chart.1.domain ∩
          cmp116SourceSigmaZero anchor).foldr (· ∪ ·) ∅ := by
  unfold CMP99GeneralizedWalk.active
  congr 1
  apply List.map_congr_left
  intro chart _
  exact cmp116SourceSigmaZeroPi4PhysicalChartDictionary_domainActive
    anchor hrange chart

/-- Named physical weakened-walk summand.  Factoring this expression avoids
re-elaborating the large dependent chart dictionary at every source-specific
terminal theorem; unfolding it recovers exactly the summand used by the
generic physical patched-walk theorem. -/
noncomputable def CMP99LabeledPhysicalChartDictionary.weakenedPhysicalPatchWalkSummand
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Nc Rrange : ℕ} [NeZero M] [NeZero Q]
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := CMP99SourcePi4Chart Label Q)
      (Label := Label) (V := FinBox 4 Q)
      (Cube := FinBox 4 (2 * Q))
      (d := 4) (N := M * (2 * Q))
      (cmp116CoarseFaceAdj 4 Q) 625 10000
      physicalBondDist Rrange)
    (K : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (left : ↥Dict.charts) (s : FinBox 4 (2 * Q) → ℝ)
    (walk : CMP99AnchoredWalk
      (cmp99PhysicalPatchSuccessorSteps Dict.charts Dict.core Dict.enlarged
        physicalBondDist Rrange) left) :
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc :=
  cmp116WeakeningMonomial (walk.active Dict.domainActive) s •
    walk.term
      (cmp99PhysicalPatchHead Dict.charts K Dict.enlarged Dict.core
        hc hmass hK)
      (fun _ => cmp99PhysicalPatchContinuation Dict.charts K
        Dict.enlarged Dict.core hc hmass hK)

set_option maxHeartbeats 800000 in
/-- Terminal source-geometry specialization of physical patched-walk
summability.  No `blockActive`, incidence budget, domain dictionary, or
active-carrier hypothesis remains: the exponent is the literal `10000` from
the `Pi^4`/`sigma_0` geometry. -/
theorem summable_cmp116SourceSigmaZeroPi4PhysicalPatchWalkSeries
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {M Q Nc Rrange NR : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q) (hsourceRange : Rrange + 1 ≤ 4 * M)
    (K : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
    (hsymm : ∀ p q : PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist p q = physicalBondDist q p)
    (hself : ∀ p : PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist p p = 0)
    (htri : ∀ x y z : PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist x y ≤
      physicalBondDist x z + physicalBondDist z y)
    {Cker c mass κ σ Ssum Sdef : ℝ}
    (hCker : 0 ≤ Cker) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ)
    (hSsum : 0 ≤ Ssum) (hSdef : 0 ≤ Sdef)
    (hsum : ∀ x,
      ∑ z : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(σ * (physicalBondDist x z : ℝ))) ≤ Ssum)
    (hsumDef : ∀ x,
      ∑ z : PhysicalBond 4 (M * (2 * Q)),
        Real.exp (-(((((κ - σ) - σ) - σ) *
          (physicalBondDist x z : ℝ)))) ≤ Sdef)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist Rrange)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => Cker))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond 4 (M * (2 * Q)),
      (Finset.univ.filter
        (fun y => physicalBondDist x y ≤ Rrange)).card ≤ NR)
    (htilt :
      (Cker + |mass|) *
          (Real.exp (κ * (Rrange : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (Δ : ℕ) (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ) :
    let Dict := cmp116SourceSigmaZeroPi4PhysicalChartDictionary
      (Label := Label) anchor hsourceRange
    ∀ (left : ↥Dict.charts)
      (s : FinBox 4 (2 * Q) → ℝ) (Rweak : ℝ)
      (hRweak : 1 ≤ Rweak)
      (hsmall :
        ((Fintype.card Label *
            (625 * 626 * Δ ^ 1250) : ℕ) : ℝ) *
            (cmp99SingleDefectDecayAmplitude
              Cker κ Rrange c mass Ssum * Sdef) *
              Rweak ^ 10000 < 1)
      (hs : s ∈ cmp116WeakeningPolydisc Rweak),
      Summable (Dict.weakenedPhysicalPatchWalkSummand
        K hc hmass hK left s) := by
  dsimp only
  intro left s Rweak hRweak hsmall hs
  simpa only [CMP99LabeledPhysicalChartDictionary.weakenedPhysicalPatchWalkSummand] using
    (CMP99LabeledPhysicalChartDictionary.summable_weakenedPhysicalPatchWalkSeries
      (G := cmp116CoarseFaceAdj 4 Q) physicalBondDist
      (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
        (Label := Label) anchor hsourceRange) K
      hsymm hself htri hCker hc hmass hσ h3σκ hSsum hSdef
      hsum hsumDef hrange hbound hK hNR htilt Δ hΔ hΔ1 left s Rweak
      hRweak hsmall hs)

end

end YangMills.RG
