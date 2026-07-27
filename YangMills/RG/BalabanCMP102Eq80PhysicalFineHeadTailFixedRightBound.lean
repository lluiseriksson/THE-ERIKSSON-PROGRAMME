/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailAbsoluteBound
import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailDomainCardinality

/-!
# Quantitative bound for the literal CMP99 fine-head/tail right factor

The domain-localized equation-(80) expansion retains, after fixing a fine
head, an ordered product of literal fine-walk defects.  This file bounds
that product from the same physical weighted-row certificate used for the
head.  In particular, no bound for the complete right factor or for a
domain activity is supplied by the caller.

The bounds remain in product form.  Their later conversion into decay in
the cardinality of the canonical physical domain uses the exact walk
budget proved in
`BalabanCMP102Eq80PhysicalFineHeadTailDomainCardinality`.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator BigOperators

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- The explicit source-produced majorant for one literal fine walk. -/
noncomputable def cmp102Eq80PhysicalFineWalkMajorant
    {Nc : ℕ} (Ahead rho rate Rweak : ℝ) (walkLength : ℕ) : ℝ :=
  Rweak ^ (10000 * (walkLength + 1)) *
    (Ahead * rho ^ walkLength *
      (((Nc ^ 2 - 1 : ℕ) : ℝ) *
        cmp99PhysicalBondGeometricRowSum 4 rate))

/-- A literal complex fine-walk term is bounded directly from the physical
weighted-row certificate and the source `Pi^4` carrier estimate. -/
theorem norm_cmp99SourcePi4ComplexFineWalkTerm_le_physicalMajorant
    {M Q Nc R walkLength : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (walk : CMP99SourcePi4FineWalkIndex M Q R walkLength) :
    ‖cmp99SourcePi4ComplexFineWalkTerm
        anchor K hc hmass hK sigma walk‖ ≤
      cmp102Eq80PhysicalFineWalkMajorant
        (Nc := Nc) Ahead rho rate Rweak walkLength := by
  have htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle +
          physicalBondDist middle source :=
    fun target source middle =>
      physicalBondDist_triangle target middle source
  have hweighted :
      PhysicalCovarianceWeightedRowKernelBound
        (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK walk)
        physicalBondDist (Ahead * rho ^ walkLength) rate := by
    change PhysicalCovarianceWeightedRowKernelBound
      ((cmp99SourcePi4FineWalkIndex.walk walk).toGeneralizedWalk.term
        (cmp99PhysicalPatchHead
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M)) hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M)) hc hmass hK))
      physicalBondDist (Ahead * rho ^ walkLength) rate
    rw [cmp99PhysicalWalkTerm_eq_orderedProduct]
    have hlen :
        walk.2.1.length = walkLength :=
      length_eq_of_mem_cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        walk.2.2
    change PhysicalCovarianceWeightedRowKernelBound
      (physicalOrderedProduct
        (cmp99PhysicalPatchHead
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M)) hc hmass hK walk.1)
        (walk.2.1.map fun step =>
          cmp99PhysicalPatchContinuation
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            K cmp99SourcePi4ChartEnlarged
            (cmp99SourcePi4ChartCore (M := M)) hc hmass hK step.domain))
      physicalBondDist (Ahead * rho ^ walkLength) rate
    simpa only [List.map_map, List.length_map, Function.comp_apply, hlen] using
      (Cert.orderedProduct_weightedRow htri walk.1
        (walk.2.1.map CMP99WalkStep.domain))
  have hop :
      ‖cmp116PhysicalEndomorphismComplexMatrix
          (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK walk)‖ ≤
        (Ahead * rho ^ walkLength) *
          (((Nc ^ 2 - 1 : ℕ) : ℝ) *
            cmp99PhysicalBondGeometricRowSum 4 rate) :=
    linfty_opNorm_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
      (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK walk)
      hrate hgeom hweighted
  have hactive :
      (cmp99SourcePi4FineWalkIndex.active anchor walk).card ≤
        10000 * (walkLength + 1) :=
    card_cmp99SourcePi4FineWalkIndex_active_le
      anchor hrange walk
  have hRweak0 : 0 ≤ Rweak := le_trans zero_le_one hRweak
  have hmonomial :
      ‖cmp116ComplexWeakeningMonomial
          (cmp99SourcePi4FineWalkIndex.active anchor walk) sigma‖ ≤
        Rweak ^ (10000 * (walkLength + 1)) := by
    have hbase :=
      norm_cmp116ComplexWeakeningMonomial_le_pow_card
        (cmp99SourcePi4FineWalkIndex.active anchor walk)
        sigma (fun _ => Rweak - 1) Rweak hRweak0
        (by
          intro d _hd
          convert hcap d using 1
          ring)
        (by
          intro d _hd
          convert le_rfl using 1
          ring)
    exact hbase.trans (pow_le_pow_right₀ hRweak hactive)
  rw [cmp99SourcePi4ComplexFineWalkTerm, norm_smul]
  exact mul_le_mul hmonomial hop (norm_nonneg _)
    (pow_nonneg hRweak0 _)

/-- Explicit majorant for one fine walk after transport into the coarse
relative defect. -/
noncomputable def cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (Ahead rho rate Rweak : ℝ) (walkLength : ℕ) : ℝ :=
  ‖cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance‖ *
    ‖cmp99SourcePi4ComplexBlockMatrix
      (M := M) (Q := Q) (Nc := Nc)‖ *
    (2 * cmp102Eq80PhysicalFineWalkMajorant
      (Nc := Nc) Ahead rho rate Rweak walkLength) *
    ‖cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)‖

/-- One literal transported coarse defect is bounded without assuming a
coarse-layer or complete-tail estimate. -/
theorem
    norm_cmp99SourcePi4ComplexCoarseFineWalkDefectTerm_le_physicalMajorant
    {M Q Nc R walkLength : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (walk : CMP99SourcePi4FineWalkIndex M Q R walkLength) :
    ‖cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
        anchor K hc hmass hK baseCoarseCovariance sigma walk‖ ≤
      cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
        (M := M) baseCoarseCovariance
        Ahead rho rate Rweak walkLength := by
  let fineSigma :=
    cmp99SourcePi4ComplexFineWalkTerm
      anchor K hc hmass hK sigma walk
  let fineOne :=
    cmp99SourcePi4ComplexFineWalkTerm
      anchor K hc hmass hK (fun _ => 1) walk
  let B :=
    cmp102Eq80PhysicalFineWalkMajorant
      (Nc := Nc) Ahead rho rate Rweak walkLength
  have hsigma : ‖fineSigma‖ ≤ B :=
    norm_cmp99SourcePi4ComplexFineWalkTerm_le_physicalMajorant
      anchor K hc hmass hK hrate hgeom Cert hrange
      sigma hRweak hcap walk
  have hone : ‖fineOne‖ ≤ B := by
    apply norm_cmp99SourcePi4ComplexFineWalkTerm_le_physicalMajorant
      anchor K hc hmass hK hrate hgeom Cert hrange
      (fun _ => 1) hRweak
    intro d
    simpa using hRweak
  have hdiff : ‖fineSigma - fineOne‖ ≤ 2 * B := by
    calc
      ‖fineSigma - fineOne‖ ≤ ‖fineSigma‖ + ‖fineOne‖ :=
        norm_sub_le _ _
      _ ≤ B + B := add_le_add hsigma hone
      _ = 2 * B := by ring
  let C0 :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  let Q0 :=
    cmp99SourcePi4ComplexBlockMatrix
      (M := M) (Q := Q) (Nc := Nc)
  let Qstar :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)
  change ‖(C0 * Q0) * (fineSigma - fineOne) * Qstar‖ ≤
    ‖C0‖ * ‖Q0‖ * (2 * B) * ‖Qstar‖
  calc
    ‖(C0 * Q0) * (fineSigma - fineOne) * Qstar‖ ≤
        ‖(C0 * Q0) * (fineSigma - fineOne)‖ * ‖Qstar‖ :=
      Matrix.linfty_opNorm_mul _ _
    _ ≤ (‖C0 * Q0‖ * ‖fineSigma - fineOne‖) * ‖Qstar‖ := by
      gcongr
      exact Matrix.linfty_opNorm_mul _ _
    _ ≤ (‖C0‖ * ‖Q0‖ * (2 * B)) * ‖Qstar‖ := by
      gcongr
      exact Matrix.linfty_opNorm_mul _ _
    _ = _ := by ring

/-- Submultiplicativity for the noncommutative `Fin`-ordered product used
by dependent coarse/fine choices. -/
theorem norm_cmp99DependentOrderedProduct_le_prod_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {n : ℕ} {α : Fin n → Type*}
    (R : ∀ i, α i → Matrix ι ι ℂ)
    (choice : ∀ i, α i) :
    ‖cmp99DependentOrderedProduct R choice‖ ≤
      ∏ i, ‖R i (choice i)‖ := by
  unfold cmp99DependentOrderedProduct cmp99OrderedFinProduct
  simpa [List.map_ofFn, List.prod_ofFn] using
    (List.norm_prod_le
      (List.ofFn fun i => R i (choice i)))

/-- The literal dependent tail word is bounded by the product of the
source-produced majorants of its selected fine walks. -/
theorem
    norm_cmp99SourcePi4ComplexCoarseFineWalkWordTerm_le_physicalMajorants
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    ‖cmp99SourcePi4ComplexCoarseFineWalkWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice‖ ≤
      ∏ i : Fin n,
        cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
          (M := M) baseCoarseCovariance
          Ahead rho rate Rweak (layerWord i) := by
  let term := fun i : Fin n =>
    -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
      anchor K hc hmass hK baseCoarseCovariance sigma (choice i)
  calc
    ‖cmp99SourcePi4ComplexCoarseFineWalkWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice‖ =
        ‖cmp99DependentOrderedProduct
          (fun i index =>
            -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
              anchor K hc hmass hK baseCoarseCovariance sigma index)
          choice‖ := rfl
    _ ≤ ∏ i : Fin n, ‖term i‖ :=
      norm_cmp99DependentOrderedProduct_le_prod_norm
        (fun i index =>
          -cmp99SourcePi4ComplexCoarseFineWalkDefectTerm
            anchor K hc hmass hK baseCoarseCovariance sigma index)
        choice
    _ ≤ ∏ i : Fin n,
          cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
            (M := M) baseCoarseCovariance
            Ahead rho rate Rweak (layerWord i) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact norm_nonneg (term i)
      · intro i _hi
        simpa [term] using
          (norm_cmp99SourcePi4ComplexCoarseFineWalkDefectTerm_le_physicalMajorant
            anchor K hc hmass hK baseCoarseCovariance
            hrate hgeom Cert hrange sigma hRweak hcap (choice i))

/-- The full fixed right factor is bounded explicitly by its two endpoint
maps and the product of all literal selected tail-walk majorants. -/
theorem
    norm_cmp99SourcePi4ComplexFineHeadTailFixedRight_le_physicalMajorants
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    ‖cmp99SourcePi4ComplexFineHeadTailFixedRight
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice‖ ≤
      ‖cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)‖ *
        (∏ i : Fin n,
          cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
            (M := M) baseCoarseCovariance
            Ahead rho rate Rweak (layerWord i)) *
        ‖cmp116PhysicalEndomorphismComplexMatrix
          baseCoarseCovariance‖ := by
  let Qstar :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)
  let word :=
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice
  let C0 :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  have hword :
      ‖word‖ ≤
        ∏ i : Fin n,
          cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
            (M := M) baseCoarseCovariance
            Ahead rho rate Rweak (layerWord i) :=
    norm_cmp99SourcePi4ComplexCoarseFineWalkWordTerm_le_physicalMajorants
      anchor K hc hmass hK baseCoarseCovariance
      hrate hgeom Cert hrange sigma hRweak hcap layerWord choice
  change ‖Qstar * word * C0‖ ≤
    ‖Qstar‖ *
      (∏ i : Fin n,
        cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
          (M := M) baseCoarseCovariance
          Ahead rho rate Rweak (layerWord i)) *
      ‖C0‖
  calc
    ‖Qstar * word * C0‖ ≤ ‖Qstar * word‖ * ‖C0‖ :=
      Matrix.linfty_opNorm_mul _ _
    _ ≤ (‖Qstar‖ * ‖word‖) * ‖C0‖ := by
      gcongr
      exact Matrix.linfty_opNorm_mul _ _
    _ ≤
        (‖Qstar‖ *
          (∏ i : Fin n,
            cmp102Eq80PhysicalCoarseFineWalkDefectMajorant
              (M := M) baseCoarseCovariance
              Ahead rho rate Rweak (layerWord i))) *
          ‖C0‖ := by
      gcongr

end

end YangMills.RG
