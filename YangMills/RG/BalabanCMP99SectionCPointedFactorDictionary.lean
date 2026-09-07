/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCellDomains
import YangMills.RG.BalabanCMP99SimpleLocalizationDomains

/-!
# The source-faithful pointed factor dictionary of CMP99 Sect. C

CMP99 does not enumerate an exhaustive family of continuation factors.  It
gives several examples, followed by "etc.", and introduces `alpha` only as an
index enumerating the possibilities.  A closed inductive enumeration would
therefore assert a source claim which is not present.

The source does specify one distinguished index completely:

* `R'_0(Pi) = h_Pi C_Pi h_Pi` for one source partition cell `Pi`;
* `R'_0(X) = 0` when the localization domain is larger than one cell.

We encode exactly that closed information by `Option Other`: `none` is the
printed index zero and `some alpha` ranges over a still-explicit finite family
of remaining factors.  The operator dictionary stores the two printed zero
equations.  Their first nontrivial consequence is proved here: every ordered
walk term with a zero-labelled non-singleton factor vanishes exactly.

Honest scope: `Other`, the nonzero factor operators, and their scale/species
compatibility remain source data to be reconstructed from the full operator
expansion.  This file neither calls the examples exhaustive nor replaces that
compatibility by an arbitrary theorem field.
-/

namespace YangMills.RG

noncomputable section

universe u v

/-- A pointed Sect. C index: the printed `0` plus an abstract remaining
finite alphabet.  This is not an exhaustive enumeration of the latter. -/
abbrev CMP99SectionCFactorLabel (Other : Type u) := Option Other

/-- The distinguished CMP99 factor index `0`. -/
def cmp99SectionCZeroLabel {Other : Type u} :
    CMP99SectionCFactorLabel Other := none

@[simp] theorem card_cmp99SectionCFactorLabel
    (Other : Type u) [Fintype Other] :
    Fintype.card (CMP99SectionCFactorLabel Other) =
      Fintype.card Other + 1 := by
  simp [CMP99SectionCFactorLabel]

/-- A source localization domain is one partition cell, rather than a larger
connected union of cells. -/
def CMP99IsSourceCellDomain {Q S : ℕ} [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) : Prop :=
  ∃ cell : FinBox 4 Q, X.blocks = {cell}

/-- The literal singleton source cell viewed in any nonzero source domain-size
budget. -/
def cmp99SourceSingletonDomainBounded {Q S : ℕ}
    [NeZero Q] [NeZero S] (cell : FinBox 4 Q) :
    CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S where
  blocks := {cell}
  nonempty := ⟨cell, by simp⟩
  connected := by
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  card_le := by
    simpa using (Nat.one_le_iff_ne_zero.mpr (NeZero.ne S))

@[simp] theorem cmp99SourceSingletonDomainBounded_blocks
    {Q S : ℕ} [NeZero Q] [NeZero S] (cell : FinBox 4 Q) :
    (cmp99SourceSingletonDomainBounded (S := S) cell).blocks = {cell} :=
  rfl

theorem cmp99IsSourceCellDomain_singleton {Q S : ℕ}
    [NeZero Q] [NeZero S]
    (cell : FinBox 4 Q) :
    CMP99IsSourceCellDomain
      (cmp99SourceSingletonDomainBounded (S := S) cell) := by
  exact ⟨cell, rfl⟩

theorem card_blocks_eq_one_of_cmp99IsSourceCellDomain
    {Q S : ℕ} [NeZero Q]
    {X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S}
    (hX : CMP99IsSourceCellDomain X) :
    X.blocks.card = 1 := by
  obtain ⟨cell, hcell⟩ := hX
  rw [hcell]
  simp

theorem not_cmp99IsSourceCellDomain_of_card_ne_one
    {Q S : ℕ} [NeZero Q]
    {X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S}
    (hcard : X.blocks.card ≠ 1) :
    ¬ CMP99IsSourceCellDomain X := by
  exact fun hX => hcard (card_blocks_eq_one_of_cmp99IsSourceCellDomain hX)

/-- The part of the Sect. C factor dictionary which CMP99 specifies without
an exhaustive list of the nonzero labels. -/
structure CMP99SectionCPointedFactorDictionary
    (Other : Type u) (Q S : ℕ) [NeZero Q] [NeZero S]
    (E : Type v) [Zero E] where
  /-- The complete operator attached to the supplied finite index. -/
  Rop : CMP99SectionCFactorLabel Other →
    CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S → E
  /-- The printed local head `h_Pi C_Pi h_Pi`. -/
  sourceCellHead : FinBox 4 Q → E
  /-- Printed identity `R'_0(Pi) = h_Pi C_Pi h_Pi`. -/
  zero_on_sourceCell : ∀ cell,
    Rop cmp99SectionCZeroLabel
      (cmp99SourceSingletonDomainBounded (S := S) cell) =
      sourceCellHead cell
  /-- Printed identity `R'_0(X) = 0` for domains larger than one cell. -/
  zero_off_sourceCell : ∀ X, ¬ CMP99IsSourceCellDomain X →
    Rop cmp99SectionCZeroLabel X = 0

namespace CMP99SectionCPointedFactorDictionary

variable {Other : Type u} {Q S : ℕ} [NeZero Q] [NeZero S]
variable {E : Type v} [MonoidWithZero E]

@[simp] theorem Rop_zero_sourceSingleton
    (Dict : CMP99SectionCPointedFactorDictionary Other Q S E)
    (cell : FinBox 4 Q) :
    Dict.Rop cmp99SectionCZeroLabel
        (cmp99SourceSingletonDomainBounded (S := S) cell) =
      Dict.sourceCellHead cell :=
  Dict.zero_on_sourceCell cell

@[simp] theorem Rop_zero_of_not_sourceCell
    (Dict : CMP99SectionCPointedFactorDictionary Other Q S E)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    (hX : ¬ CMP99IsSourceCellDomain X) :
    Dict.Rop cmp99SectionCZeroLabel X = 0 :=
  Dict.zero_off_sourceCell X hX

/-- The distinguished head factor kills a generalized walk whose initial
domain is not a single source cell. -/
theorem term_eq_zero_of_head_not_sourceCell
    (Dict : CMP99SectionCPointedFactorDictionary Other Q S E)
    (walk : CMP99GeneralizedWalk (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S))
    (hhead : ¬ CMP99IsSourceCellDomain walk.head) :
    walk.term (Dict.Rop cmp99SectionCZeroLabel) Dict.Rop = 0 := by
  simp [CMP99GeneralizedWalk.term, Dict.zero_off_sourceCell _ hhead]

/-- Any continuation carrying the distinguished zero label on a domain larger
than one cell kills the complete ordered noncommutative walk product. -/
theorem term_eq_zero_of_zero_tail_step_not_sourceCell
    (Dict : CMP99SectionCPointedFactorDictionary Other Q S E)
    (walk : CMP99GeneralizedWalk (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S))
    (step : CMP99WalkStep (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S))
    (hstep : step ∈ walk.tail)
    (hzero : step.label = cmp99SectionCZeroLabel)
    (hdomain : ¬ CMP99IsSourceCellDomain step.domain) :
    walk.term (Dict.Rop cmp99SectionCZeroLabel) Dict.Rop = 0 := by
  have hfactor : Dict.Rop step.label step.domain = 0 := by
    rw [hzero]
    exact Dict.zero_off_sourceCell step.domain hdomain
  have hmem : (0 : E) ∈ walk.tail.map
      (fun next => Dict.Rop next.label next.domain) := by
    exact List.mem_map.mpr ⟨step, hstep, hfactor⟩
  rw [CMP99GeneralizedWalk.term]
  simp [List.prod_eq_zero hmem]

end CMP99SectionCPointedFactorDictionary

section SourceAllowedSuccessors

variable {Other : Type u} [Fintype Other] [DecidableEq Other]
variable {Q S : ℕ} [NeZero Q] [NeZero S]

/-- The part of source admissibility fixed by the printed zero-factor
equations: a zero-labelled continuation must have a singleton domain. -/
def cmp99SectionCZeroCompatibleStep
    (step : CMP99WalkStep (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)) : Prop :=
  step.label ≠ cmp99SectionCZeroLabel ∨
    CMP99IsSourceCellDomain step.domain

/-- Source-safe successor overcount with the impossible zero-labelled larger
domains removed.  The still-open scale compatibility may filter it further. -/
noncomputable def cmp99SectionCZeroCompatibleSuccessors
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    Finset (CMP99WalkStep (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)) := by
  classical
  exact (cmp99SimpleDomainSuccessors
    (Label := CMP99SectionCFactorLabel Other)
    (cmp116CoarseFaceAdj 4 Q) S X).filter cmp99SectionCZeroCompatibleStep

theorem mem_cmp99SectionCZeroCompatibleSuccessors_iff
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    (step : CMP99WalkStep (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)) :
    step ∈ cmp99SectionCZeroCompatibleSuccessors X ↔
      step ∈ cmp99SimpleDomainSuccessors
        (Label := CMP99SectionCFactorLabel Other)
        (cmp116CoarseFaceAdj 4 Q) S X ∧
      (step.label ≠ cmp99SectionCZeroLabel ∨
        CMP99IsSourceCellDomain step.domain) := by
  classical
  simp [cmp99SectionCZeroCompatibleSuccessors,
    cmp99SectionCZeroCompatibleStep]

/-- A tail step removed by the source zero-compatibility filter contributes
an exact zero factor, hence kills the complete ordered walk term. -/
theorem CMP99SectionCPointedFactorDictionary.term_eq_zero_of_tail_step_not_zeroCompatible
    {E : Type v} [MonoidWithZero E]
    (Dict : CMP99SectionCPointedFactorDictionary Other Q S E)
    (walk : CMP99GeneralizedWalk (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S))
    (step : CMP99WalkStep (CMP99SectionCFactorLabel Other)
      (CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S))
    (hstep : step ∈ walk.tail)
    (hnot : ¬ cmp99SectionCZeroCompatibleStep step) :
    walk.term (Dict.Rop cmp99SectionCZeroLabel) Dict.Rop = 0 := by
  have hzero : step.label = cmp99SectionCZeroLabel := by
    by_contra hne
    exact hnot (Or.inl hne)
  have hdomain : ¬ CMP99IsSourceCellDomain step.domain := by
    intro hsource
    exact hnot (Or.inr hsource)
  exact Dict.term_eq_zero_of_zero_tail_step_not_sourceCell
    walk step hstep hzero hdomain

/-- Removing the source-forbidden zero factors preserves the established
volume-uniform branching majorant. -/
theorem card_cmp99SectionCZeroCompatibleSuccessors_le
    (Δ : ℕ) (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (cmp99SectionCZeroCompatibleSuccessors
      (Other := Other) X).card ≤
      Fintype.card (CMP99SectionCFactorLabel Other) *
        (S * (S + 1) * Δ ^ (2 * S)) := by
  classical
  calc
    (cmp99SectionCZeroCompatibleSuccessors (Other := Other) X).card ≤
        (cmp99SimpleDomainSuccessors
          (Label := CMP99SectionCFactorLabel Other)
          (cmp116CoarseFaceAdj 4 Q) S X).card :=
      by
        rw [cmp99SectionCZeroCompatibleSuccessors]
        exact Finset.card_filter_le _ _
    _ ≤ Fintype.card (CMP99SectionCFactorLabel Other) *
        (S * (S + 1) * Δ ^ (2 * S)) :=
      card_cmp99SimpleDomainSuccessors_le
        (Label := CMP99SectionCFactorLabel Other)
        (cmp116CoarseFaceAdj 4 Q) S Δ hΔ hΔ1 X

end SourceAllowedSuccessors

end

end YangMills.RG
