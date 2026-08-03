/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma1MultiplicityPropagatorBound
import YangMills.RG.BalabanCMP99ComplexFineHeadTailMultiplicitySeries

/-!
# Physical minimizer specialization of CMP116 Lemma 1 L1

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its results have not yet been verified by the Lean compiler.

The literal physical minimizer is stored as the nested series

`Neumann length -> coarse word -> tail choice -> head length -> head walk
  -> omitted subset`.

This module flattens exactly those six coordinates into one dependent walk
type and specializes the multiplicity-aware L1 certificate entrywise.  The
sign of an omitted subset stays in the sigma-independent term, while every
retained weakening occurrence stays in the multiplicity.  Radial summability
from the certificate justifies each dependent `tsum` reindexing.

Honest scope: the source still has to construct the certificate uniformly in
the matrix entries.  In particular it must pay the finite powerset cost in
the post-expansion base weight and prove the total-degree/tree-length
geometry.  This file neither identifies total degree with the printed CMP116
integer `m`, nor proves coordinatewise holomorphy, nor constructs `H0(s)`.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- One term of the fully expanded literal physical minimizer, retaining all
six source coordinates in their original order. -/
abbrev CMP116Lemma1PhysicalMinimizerWalk
    (M Q R : ℕ) [NeZero M] [NeZero Q] :=
  Σ neumannLength : ℕ,
    Σ layerWord : Fin neumannLength → ℕ,
      Σ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        Σ headLength : ℕ,
          Σ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
            Finset (Fin neumannLength)

/-- Exact retained weakening multiplicity of one expanded physical term. -/
noncomputable def cmp116Lemma1PhysicalMinimizerWalkMultiplicity
    {M Q R : ℕ} [NeZero M] [NeZero Q]
    (anchor : FinBox 4 Q)
    (walk : CMP116Lemma1PhysicalMinimizerWalk M Q R) :
    FinBox 4 (2 * Q) →₀ ℕ :=
  cmp99SourcePi4ComplexFineHeadTailMultiplicity
    anchor walk.2.2.2.2.1 walk.2.2.1
      (Finset.univ \ walk.2.2.2.2.2)

/-- Sigma-independent scalar entry of one expanded physical term.  The
omitted-subset sign is part of the term, not of the positive base weight. -/
noncomputable def cmp116Lemma1PhysicalMinimizerWalkEntryTerm
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarsePhysicalOneCochain 4 (2 * Q) Nc →L[ℝ]
        CoarsePhysicalOneCochain 4 (2 * Q) Nc)
    (row : FineCoord M Q Nc) (col : CoarseCoord Q Nc)
    (walk : CMP116Lemma1PhysicalMinimizerWalk M Q R) : ℂ :=
  (-1 : ℂ) ^ walk.2.2.2.2.2.card *
    cmp99SourcePi4ComplexFineHeadTailWordBase
      K hc hmass hK baseCoarseCovariance
      walk.2.2.2.2.1 walk.2.2.1 row col

/-- One flattened multiplicity term is exactly the corresponding scalar
entry of the literal omitted-subset summand. -/
theorem cmp116Lemma1PhysicalMinimizerWalkEntryTerm_eq
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarsePhysicalOneCochain 4 (2 * Q) Nc →L[ℝ]
        CoarsePhysicalOneCochain 4 (2 * Q) Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (row : FineCoord M Q Nc) (col : CoarseCoord Q Nc)
    (walk : CMP116Lemma1PhysicalMinimizerWalk M Q R) :
    cmp116ComplexWeakeningMultiplicityMonomial
        (cmp116Lemma1PhysicalMinimizerWalkMultiplicity anchor walk) sigma •
      cmp116Lemma1PhysicalMinimizerWalkEntryTerm
        K hc hmass hK baseCoarseCovariance row col walk =
      (((-1 : ℂ) ^ walk.2.2.2.2.2.card *
          cmp116ComplexWeakeningMultiplicityMonomial
            (cmp99SourcePi4ComplexFineHeadTailMultiplicity
              anchor walk.2.2.2.2.1 walk.2.2.1
                (Finset.univ \ walk.2.2.2.2.2)) sigma) •
        cmp99SourcePi4ComplexFineHeadTailWordBase
          K hc hmass hK baseCoarseCovariance
          walk.2.2.2.2.1 walk.2.2.1) row col := by
  change
    cmp116ComplexWeakeningMultiplicityMonomial
          (cmp116Lemma1PhysicalMinimizerWalkMultiplicity anchor walk) sigma *
        (((-1 : ℂ) ^ walk.2.2.2.2.2.card *
          cmp99SourcePi4ComplexFineHeadTailWordBase
            K hc hmass hK baseCoarseCovariance
            walk.2.2.2.2.1 walk.2.2.1 row col) =
      (((-1 : ℂ) ^ walk.2.2.2.2.2.card *
          cmp116ComplexWeakeningMultiplicityMonomial
            (cmp99SourcePi4ComplexFineHeadTailMultiplicity
              anchor walk.2.2.2.2.1 walk.2.2.1
                (Finset.univ \ walk.2.2.2.2.2)) sigma) *
        cmp99SourcePi4ComplexFineHeadTailWordBase
          K hc hmass hK baseCoarseCovariance
          walk.2.2.2.2.1 walk.2.2.1 row col)
  rfl

/-- Matrix assembled entrywise from the multiplicity-aware L1 certificates
on the flattened physical walk type. -/
noncomputable def cmp116Lemma1PhysicalMinimizerPropagator
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarsePhysicalOneCochain 4 (2 * Q) Nc →L[ℝ]
        CoarsePhysicalOneCochain 4 (2 * Q) Nc)
    {treeLength : CMP116Lemma1PhysicalMinimizerWalk M Q R → ℕ}
    {baseWeight : CMP116Lemma1PhysicalMinimizerWalk M Q R → ℝ}
    {B0 delta0 delta1 kappa1 : ℝ}
    (C : ∀ row col,
      CMP116Lemma1MultiplicityPropagatorCertificate
        (cmp116Lemma1PhysicalMinimizerWalkMultiplicity anchor)
        (cmp116Lemma1PhysicalMinimizerWalkEntryTerm
          K hc hmass hK baseCoarseCovariance row col)
        treeLength baseWeight B0 delta0 delta1 (M : ℝ) kappa1)
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  fun row col ↦ (C row col).propagator sigma

/-- The flattened physical L1 propagator is exactly the complete nested
multiplicity series, entry by entry.  Every dependent reindexing is justified
by the radial summability already carried by the certificate. -/
theorem cmp116Lemma1PhysicalMinimizerPropagator_eq_nestedMultiplicitySeries
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarsePhysicalOneCochain 4 (2 * Q) Nc →L[ℝ]
        CoarsePhysicalOneCochain 4 (2 * Q) Nc)
    {treeLength : CMP116Lemma1PhysicalMinimizerWalk M Q R → ℕ}
    {baseWeight : CMP116Lemma1PhysicalMinimizerWalk M Q R → ℝ}
    {B0 delta0 delta1 kappa1 : ℝ}
    (C : ∀ row col,
      CMP116Lemma1MultiplicityPropagatorCertificate
        (cmp116Lemma1PhysicalMinimizerWalkMultiplicity anchor)
        (cmp116Lemma1PhysicalMinimizerWalkEntryTerm
          K hc hmass hK baseCoarseCovariance row col)
        treeLength baseWeight B0 delta0 delta1 (M : ℝ) kappa1)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1) :
    cmp116Lemma1PhysicalMinimizerPropagator
        anchor K hc hmass hK baseCoarseCovariance C sigma =
      ∑' neumannLength : ℕ,
        ∑' layerWord : Fin neumannLength → ℕ,
          ∑ choice : CMP99SourcePi4CoarseFineWalkChoice
              M Q R layerWord,
            ∑' headLength : ℕ,
              ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
                ∑ omitted ∈
                    (Finset.univ : Finset (Fin neumannLength)).powerset,
                  (((-1 : ℂ) ^ omitted.card *
                    cmp116ComplexWeakeningMultiplicityMonomial
                      (cmp99SourcePi4ComplexFineHeadTailMultiplicity
                        anchor head choice
                          (Finset.univ \ omitted)) sigma) •
                    cmp99SourcePi4ComplexFineHeadTailWordBase
                      K hc hmass hK baseCoarseCovariance
                      head choice := by
  classical
  ext row col
  let f : CMP116Lemma1PhysicalMinimizerWalk M Q R → ℂ := fun walk ↦
    cmp116ComplexWeakeningMultiplicityMonomial
        (cmp116Lemma1PhysicalMinimizerWalkMultiplicity anchor walk) sigma •
      cmp116Lemma1PhysicalMinimizerWalkEntryTerm
        K hc hmass hK baseCoarseCovariance row col walk
  have hflat : Summable f := by
    exact summable_cmp116ComplexWeakeningMultiplicitySeries
      (cmp116Lemma1PhysicalMinimizerWalkMultiplicity anchor)
      (cmp116Lemma1PhysicalMinimizerWalkEntryTerm
        K hc hmass hK baseCoarseCovariance row col)
      sigma (Real.exp kappa1) (fun _walk d _hd ↦ hsigma d)
      (C row col).summable_radialMajorant
  calc
    cmp116Lemma1PhysicalMinimizerPropagator
          anchor K hc hmass hK baseCoarseCovariance C sigma row col =
        ∑' walk : CMP116Lemma1PhysicalMinimizerWalk M Q R, f walk := by
      rfl
    _ = ∑' neumannLength : ℕ,
        ∑' layerWord : Fin neumannLength → ℕ,
          ∑' choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
            ∑' headLength : ℕ,
              ∑' head : CMP99SourcePi4FineWalkIndex M Q R headLength,
                ∑' omitted : Finset (Fin neumannLength),
                  f ⟨neumannLength, layerWord, choice,
                    headLength, head, omitted⟩ := by
      rw [hflat.tsum_sigma]
      apply tsum_congr
      intro neumannLength
      have h1 := hflat.sigma neumannLength
      rw [h1.tsum_sigma]
      apply tsum_congr
      intro layerWord
      have h2 := h1.sigma layerWord
      rw [h2.tsum_sigma]
      apply tsum_congr
      intro choice
      have h3 := h2.sigma choice
      rw [h3.tsum_sigma]
      apply tsum_congr
      intro headLength
      have h4 := h3.sigma headLength
      rw [h4.tsum_sigma]
    _ = ∑' neumannLength : ℕ,
        ∑' layerWord : Fin neumannLength → ℕ,
          ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
            ∑' headLength : ℕ,
              ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
                ∑ omitted : Finset (Fin neumannLength),
                  f ⟨neumannLength, layerWord, choice,
                    headLength, head, omitted⟩ := by
      apply tsum_congr
      intro neumannLength
      apply tsum_congr
      intro layerWord
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro choice _hchoice
      apply tsum_congr
      intro headLength
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro head _hhead
      rw [tsum_fintype]
    _ = ∑' neumannLength : ℕ,
        ∑' layerWord : Fin neumannLength → ℕ,
          ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
            ∑' headLength : ℕ,
              ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
                ∑ omitted ∈
                    (Finset.univ : Finset (Fin neumannLength)).powerset,
                  (((-1 : ℂ) ^ omitted.card *
                    cmp116ComplexWeakeningMultiplicityMonomial
                      (cmp99SourcePi4ComplexFineHeadTailMultiplicity
                        anchor head choice
                          (Finset.univ \ omitted)) sigma) •
                    cmp99SourcePi4ComplexFineHeadTailWordBase
                      K hc hmass hK baseCoarseCovariance
                      head choice row col := by
      apply tsum_congr
      intro neumannLength
      apply tsum_congr
      intro layerWord
      apply Finset.sum_congr rfl
      intro choice _hchoice
      apply tsum_congr
      intro headLength
      apply Finset.sum_congr rfl
      intro head _hhead
      rw [Finset.powerset_univ]
      apply Finset.sum_congr rfl
      intro omitted _homitted
      exact cmp116Lemma1PhysicalMinimizerWalkEntryTerm_eq
        anchor K hc hmass hK baseCoarseCovariance sigma row col
          ⟨neumannLength, layerWord, choice, headLength, head, omitted⟩
    _ = (∑' neumannLength : ℕ,
        ∑' layerWord : Fin neumannLength → ℕ,
          ∑ choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
            ∑' headLength : ℕ,
              ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
                ∑ omitted ∈
                    (Finset.univ : Finset (Fin neumannLength)).powerset,
                  (((-1 : ℂ) ^ omitted.card *
                    cmp116ComplexWeakeningMultiplicityMonomial
                      (cmp99SourcePi4ComplexFineHeadTailMultiplicity
                        anchor head choice
                          (Finset.univ \ omitted)) sigma) •
                    cmp99SourcePi4ComplexFineHeadTailWordBase
                      K hc hmass hK baseCoarseCovariance
                      head choice) row col := by
      simp only [Matrix.tsum_apply, Matrix.sum_apply]

end

end YangMills.RG
