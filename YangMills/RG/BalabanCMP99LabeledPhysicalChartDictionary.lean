/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalChartDictionary

/-!
# Factor-labelled physical CMP99 chart dictionary

CMP99 generalized walks use steps `(alpha, X)`.  Distinct operator-factor
labels may therefore share the same geometric localization domain.  Requiring
`domainOf` itself to be injective would discard this source index.

This file gives the source-faithful dictionary: the pair
`(factorLabel, domainOf)` is injective.  Physical successors inject into the
already constructed family containing every label paired with every meeting
simple domain.  The resulting uniform branching constant is

`card Label * S * (S + 1) * Delta^(2*S)`.

The unlabelled dictionary remains a valid specialization when the geometric
domain alone determines the chart.
-/

namespace YangMills.RG

noncomputable section

universe u v w

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Source-faithful physical chart certificate retaining the CMP99 factor
label. -/
structure CMP99LabeledPhysicalChartDictionary
    {ι : Type*} [DecidableEq ι]
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {V : Type v} [Fintype V] [DecidableEq V]
    {Cube : Type w} [DecidableEq Cube]
    {d N : ℕ} [NeZero N]
    (G : SimpleGraph V) (S B : ℕ)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (Rrange : ℕ) where
  charts : Finset ι
  core : ι → Finset (PhysicalBond d N)
  enlarged : ι → Finset (PhysicalBond d N)
  factorLabel : ↥charts → Label
  domainOf : ↥charts → CMP99SimpleLocalizationDomain G S
  domainActive : ↥charts → Finset Cube
  core_subset_enlarged : ∀ i, i ∈ charts → core i ⊆ enlarged i
  labeledDomain_injective : Function.Injective fun chart =>
    (factorLabel chart, domainOf chart)
  near_implies_meets : ∀ (left right : ↥charts),
    CMP99PhysicalPatchCanFollow core enlarged dist Rrange left right →
      (domainOf left).Meets (domainOf right)
  active_card_le : ∀ X, (domainActive X).card ≤ B

namespace CMP99LabeledPhysicalChartDictionary

variable {ι : Type*} [DecidableEq ι]
variable {Label : Type u} [Fintype Label] [DecidableEq Label]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {Cube : Type w} [DecidableEq Cube]
variable {d N : ℕ} [NeZero N]
variable {G : SimpleGraph V} {S B Rrange : ℕ}
variable {dist : PhysicalBond d N → PhysicalBond d N → ℕ}

/-- The literal `(alpha, X)` generalized-walk step attached to a physical
chart. -/
def sourceStep
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B dist Rrange)
    (chart : ↥Dict.charts) :
    CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S) :=
  ⟨Dict.factorLabel chart, Dict.domainOf chart⟩

theorem sourceStep_injective
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B dist Rrange) :
    Function.Injective (sourceStep (ι := ι) (Label := Label) (V := V)
      (Cube := Cube) (d := d) (N := N) Dict) := by
  intro left right hEq
  apply Dict.labeledDomain_injective
  exact congrArg (fun step => (step.label, step.domain)) hEq

/-- Every physical near-range successor maps to the source-safe family of all
labels paired with all simple domains meeting the current domain. -/
theorem image_physicalSuccessors_sourceStep_subset
    [DecidableRel G.Adj]
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B dist Rrange)
    (left : ↥Dict.charts) :
    (cmp99PhysicalPatchSuccessors
      Dict.charts Dict.core Dict.enlarged dist Rrange left).image
        (sourceStep (ι := ι) (Label := Label) (V := V) (Cube := Cube)
          (d := d) (N := N) Dict) ⊆
      cmp99SimpleDomainSuccessors (Label := Label) G S (Dict.domainOf left) := by
  intro step hstep
  simp only [Finset.mem_image] at hstep
  obtain ⟨right, hright, rfl⟩ := hstep
  rw [cmp99SimpleDomainSuccessors, Finset.mem_image]
  refine ⟨(Dict.factorLabel right, Dict.domainOf right), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, by
    rw [cmp99MeetingSimpleDomains, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Dict.near_implies_meets left right
      ((mem_cmp99PhysicalPatchSuccessors_iff
        Dict.charts Dict.core Dict.enlarged dist Rrange left right).mp hright)⟩⟩

/-- Correct labelled, volume-uniform physical branching bound. -/
theorem card_physicalSuccessors_le_labeledSimpleDomainBound
    [DecidableRel G.Adj]
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B dist Rrange)
    (Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (left : ↥Dict.charts) :
    (cmp99PhysicalPatchSuccessors
      Dict.charts Dict.core Dict.enlarged dist Rrange left).card ≤
      Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S)) := by
  calc
    (cmp99PhysicalPatchSuccessors
        Dict.charts Dict.core Dict.enlarged dist Rrange left).card =
      ((cmp99PhysicalPatchSuccessors
        Dict.charts Dict.core Dict.enlarged dist Rrange left).image
          (sourceStep (ι := ι) (Label := Label) (V := V) (Cube := Cube)
            (d := d) (N := N) Dict)).card := by
        symm
        exact Finset.card_image_of_injective _
          (sourceStep_injective (ι := ι) (Label := Label) (V := V)
            (Cube := Cube) (d := d) (N := N) Dict)
    _ ≤ (cmp99SimpleDomainSuccessors
        (Label := Label) G S (Dict.domainOf left)).card :=
      Finset.card_le_card
        (image_physicalSuccessors_sourceStep_subset (ι := ι) (Label := Label)
          (V := V) (Cube := Cube) (d := d) (N := N) Dict left)
    _ ≤ Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S)) :=
      card_cmp99SimpleDomainSuccessors_le G S Δ hΔ hΔ1 (Dict.domainOf left)

/-- The same labelled bound for the unique-species patched continuation
steps.  `Unit` records the patched defect species; the source factor label is
retained in the dictionary count. -/
theorem card_physicalSuccessorSteps_le_labeledSimpleDomainBound
    [DecidableRel G.Adj]
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B dist Rrange)
    (Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (left : ↥Dict.charts) :
    (cmp99PhysicalPatchSuccessorSteps
      Dict.charts Dict.core Dict.enlarged dist Rrange left).card ≤
      Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S)) := by
  rw [card_cmp99PhysicalPatchSuccessorSteps]
  exact card_physicalSuccessors_le_labeledSimpleDomainBound
    (ι := ι) (Label := Label) (V := V) (Cube := Cube)
    (d := d) (N := N) Dict Δ hΔ hΔ1 left

/-- Length-`n` physical tails inherit the corrected labelled branching
constant. -/
theorem card_physicalAdmissibleTails_le_pow_labeledSimpleDomainBound
    [DecidableRel G.Adj]
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B dist Rrange)
    (Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (n : ℕ) (left : ↥Dict.charts) :
    (cmp99AdmissibleTails
      (cmp99PhysicalPatchSuccessorSteps
        Dict.charts Dict.core Dict.enlarged dist Rrange) left n).card ≤
      (Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S))) ^ n := by
  exact card_cmp99AdmissibleTails_le_pow
    (cmp99PhysicalPatchSuccessorSteps
      Dict.charts Dict.core Dict.enlarged dist Rrange)
    (Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S)))
    (fun current => card_physicalSuccessorSteps_le_labeledSimpleDomainBound
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) Dict Δ hΔ hΔ1 current)
    n left

end CMP99LabeledPhysicalChartDictionary

section LabeledDictionarySummability

variable {V : Type v} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {Cube : Type w} [DecidableEq Cube]

/-- Terminal physical summability theorem retaining the source CMP99 factor
label in the branching count.  The physical patched continuation has one
operator species per chart, while distinct charts may carry distinct source
factor labels over the same geometric domain. -/
theorem CMP99LabeledPhysicalChartDictionary.summable_weakenedPhysicalPatchWalkSeries
    {ι : Type*} [DecidableEq ι]
    {Label : Type u} [Fintype Label] [DecidableEq Label]
    {d N Nc : ℕ} [NeZero N]
    {S B Rrange NR : ℕ}
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (Dict : CMP99LabeledPhysicalChartDictionary
      (ι := ι) (Label := Label) (V := V) (Cube := Cube)
      (d := d) (N := N) G S B dist Rrange)
    (K : PhysicalEndomorphism d N Nc)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {M c mass κ σ Ssum Sdef : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ)
    (hSsum : 0 ≤ Ssum) (hSdef : 0 ≤ Sdef)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hsumDef : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(((((κ - σ) - σ) - σ) * (dist x z : ℝ)))) ≤ Sdef)
    (hrange : PhysicalCovarianceFiniteRange K dist Rrange)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ Rrange)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (Rrange : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (left : ↥Dict.charts) (s : Cube → ℝ) (Rweak : ℝ)
    (hRweak : 1 ≤ Rweak)
    (hsmall :
      ((Fintype.card Label *
          (S * (S + 1) * Δ ^ (2 * S)) : ℕ) : ℝ) *
          (cmp99SingleDefectDecayAmplitude
            M κ Rrange c mass Ssum * Sdef) * Rweak ^ B < 1)
    (hs : s ∈ cmp116WeakeningPolydisc Rweak) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99PhysicalPatchSuccessorSteps
          (ι := ι) (d := d) (N := N)
          Dict.charts Dict.core Dict.enlarged dist Rrange) left =>
      cmp116WeakeningMonomial (walk.active Dict.domainActive) s •
        walk.term
          (cmp99PhysicalPatchHead
            Dict.charts K Dict.enlarged Dict.core hc hmass hK)
          (fun _ => cmp99PhysicalPatchContinuation
            Dict.charts K Dict.enlarged Dict.core hc hmass hK) := by
  have hmin : 0 < min c mass := lt_min hc hmass
  have hAmp : 0 ≤ cmp99SingleDefectDecayAmplitude
      M κ Rrange c mass Ssum := by
    dsimp [cmp99SingleDefectDecayAmplitude]
    positivity
  exact summable_cmp116WeakenedCMP99WalkSeries
    (cmp99PhysicalPatchSuccessorSteps
      Dict.charts Dict.core Dict.enlarged dist Rrange)
    left Dict.domainActive
    (cmp99PhysicalPatchHead Dict.charts K Dict.enlarged Dict.core hc hmass hK)
    (fun _ => cmp99PhysicalPatchContinuation
      Dict.charts K Dict.enlarged Dict.core hc hmass hK)
    s (Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S))) B
    (min c mass)⁻¹
    (cmp99SingleDefectDecayAmplitude M κ Rrange c mass Ssum * Sdef)
    Rweak
    (fun current =>
      CMP99LabeledPhysicalChartDictionary.card_physicalSuccessorSteps_le_labeledSimpleDomainBound
        (ι := ι) (Label := Label) (V := V) (Cube := Cube)
        (d := d) (N := N) Dict Δ hΔ hΔ1 current)
    Dict.active_card_le (inv_nonneg.mpr hmin.le) (mul_nonneg hAmp hSdef)
    hRweak hsmall
    (fun walk => norm_cmp99PhysicalAnchoredPatchWalk_term_le
      Dict.charts K Dict.enlarged Dict.core Dict.core_subset_enlarged
      dist hsymm hself htri hM hc hmass hσ h3σκ hSsum hSdef
      hsum hsumDef hrange hbound hK hNR htilt left walk)
    hs

end LabeledDictionarySummability

end

end YangMills.RG
