/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailAnchoredLocalization
import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredLocalizationBound

/-!
# Absolute bounds for literal CMP99 fine-head/tail terms

The length-layer summability used by the minimizer reconstruction is not by
itself enough to exchange the head-length sum with localization by physical
domains: cancellation may occur inside a layer.  Here the physical
weighted-row certificate is applied before the finite head sum.  This gives
an absolute geometric majorant for every literal rectangular head-tail
matrix term.

The fixed coarse tail is retained literally.  No bound for a complete
localized activity is assumed.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

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

/-- The fixed right factor multiplying every fine head in one dependent
coarse choice. -/
noncomputable def cmp99SourcePi4ComplexFineHeadTailFixedRight
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc) *
    cmp99SourcePi4ComplexCoarseFineWalkWordTerm
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice *
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance

/-- One literal rectangular head-tail matrix is the fine head multiplied by
the fixed right factor. -/
theorem cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_mul_fixedRight
    {M Q Nc R headLength n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice =
      cmp99SourcePi4ComplexFineWalkTerm
          anchor K hc hmass hK sigma head *
        cmp99SourcePi4ComplexFineHeadTailFixedRight
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice := by
  simp [cmp99SourcePi4ComplexFineHeadTailWordTerm,
    cmp99SourcePi4ComplexFineHeadTailFixedRight, Matrix.mul_assoc]

private theorem sourcePi4UnitDomain_injective_for_fine_head_absolute
    {Q : ℕ} [NeZero Q] :
    Function.Injective
      (fun chart : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)) => chart.1.domain) := by
  rintro ⟨⟨leftLabel, leftDomain⟩, hleft⟩
    ⟨⟨rightLabel, rightDomain⟩, hright⟩ hEq
  cases leftLabel
  cases rightLabel
  apply Subtype.ext
  cases hEq
  rfl

/-- The norm of one literal fine-head/tail matrix is controlled before any
finite sum over heads is taken. -/
theorem norm_cmp99SourcePi4ComplexFineHeadTailWordTerm_le
    {M Q Nc R headLength n : ℕ}
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
    (head : CMP99SourcePi4FineWalkIndex M Q R headLength)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
        anchor K hc hmass hK baseCoarseCovariance
        sigma head layerWord choice‖ ≤
      (Rweak ^ (10000 * (headLength + 1)) *
        (Ahead * rho ^ headLength *
          (((Nc ^ 2 - 1 : ℕ) : ℝ) *
            cmp99PhysicalBondGeometricRowSum 4 rate))) *
        ‖cmp99SourcePi4ComplexFineHeadTailFixedRight
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice‖ := by
  have htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle +
          physicalBondDist middle source :=
    fun target source middle =>
      physicalBondDist_triangle target middle source
  have hweighted :
      PhysicalCovarianceWeightedRowKernelBound
        (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK head)
        physicalBondDist (Ahead * rho ^ headLength) rate := by
    change PhysicalCovarianceWeightedRowKernelBound
      ((cmp99SourcePi4FineWalkIndex.walk head).toGeneralizedWalk.term
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
      physicalBondDist (Ahead * rho ^ headLength) rate
    rw [cmp99PhysicalWalkTerm_eq_orderedProduct]
    have hlen :
        head.2.1.length = headLength :=
      length_eq_of_mem_cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        head.2.2
    change PhysicalCovarianceWeightedRowKernelBound
      (physicalOrderedProduct
        (cmp99PhysicalPatchHead
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M)) hc hmass hK head.1)
        (head.2.1.map fun step =>
          cmp99PhysicalPatchContinuation
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            K cmp99SourcePi4ChartEnlarged
            (cmp99SourcePi4ChartCore (M := M)) hc hmass hK step.domain))
      physicalBondDist (Ahead * rho ^ headLength) rate
    simpa only [List.map_map, List.length_map, Function.comp_apply, hlen] using
      (Cert.orderedProduct_weightedRow htri head.1
        (head.2.1.map CMP99WalkStep.domain))
  have hop :
      ‖cmp116PhysicalEndomorphismComplexMatrix
          (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK head)‖ ≤
        (Ahead * rho ^ headLength) *
          (((Nc ^ 2 - 1 : ℕ) : ℝ) *
            cmp99PhysicalBondGeometricRowSum 4 rate) :=
    linfty_opNorm_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
      (cmp99SourcePi4FineWalkIndex.operator K hc hmass hK head)
      hrate hgeom hweighted
  have hactive :
      (cmp99SourcePi4FineWalkIndex.active anchor head).card ≤
        10000 * (headLength + 1) := by
    have hchart :
        ∀ chart : ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)),
          (cmp99SourceDomainLargeBlocks chart.1.domain ∩
            cmp116SourceSigmaZero anchor).card ≤ 10000 := by
      intro chart
      simpa using
        (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
          (Label := Unit) anchor hrange).active_card_le chart
    simpa [cmp99SourcePi4FineWalkIndex.active,
      cmp99SourcePi4FineWalkIndex.walk,
      CMP99AnchoredWalk.active] using
      ((cmp99SourcePi4FineWalkIndex.walk head).card_active_le_mul_length_add_one
        (fun chart =>
          cmp99SourceDomainLargeBlocks chart.1.domain ∩
            cmp116SourceSigmaZero anchor)
        10000 hchart)
  have hRweak0 : 0 ≤ Rweak := le_trans zero_le_one hRweak
  have hmonomial :
      ‖cmp116ComplexWeakeningMonomial
          (cmp99SourcePi4FineWalkIndex.active anchor head) sigma‖ ≤
        Rweak ^ (10000 * (headLength + 1)) := by
    have hbase :=
      norm_cmp116ComplexWeakeningMonomial_le_pow_card
        (cmp99SourcePi4FineWalkIndex.active anchor head)
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
  have hfine :
      ‖cmp99SourcePi4ComplexFineWalkTerm
          anchor K hc hmass hK sigma head‖ ≤
        Rweak ^ (10000 * (headLength + 1)) *
          (Ahead * rho ^ headLength *
            (((Nc ^ 2 - 1 : ℕ) : ℝ) *
              cmp99PhysicalBondGeometricRowSum 4 rate)) := by
    rw [cmp99SourcePi4ComplexFineWalkTerm, norm_smul]
    exact mul_le_mul hmonomial hop (norm_nonneg _)
      (pow_nonneg hRweak0 _)
  rw [cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_mul_fixedRight]
  exact (Matrix.linfty_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right hfine (norm_nonneg _))

/-- The sum of the norms of all literal rectangular terms in a fixed head
layer is summable over the head length.  This is stronger than summability
of the already-summed matrix layers and therefore survives restriction to
an arbitrary physical-domain fiber. -/
theorem
    summable_sum_norm_cmp99SourcePi4ComplexFineHeadTailWordTerm
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord) :
    Summable fun headLength : ℕ =>
      ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
        ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
          anchor K hc hmass hK baseCoarseCovariance
          sigma head layerWord choice‖ := by
  let branch : ℕ := cmp116SourcePi4TerminalBranching Δ
  let q : ℝ := cmp116SourcePi4ComplexContourRatio Δ rho Rweak
  let rowMass : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate
  let right :=
    cmp99SourcePi4ComplexFineHeadTailFixedRight
      anchor K hc hmass hK baseCoarseCovariance
      sigma layerWord choice
  let prefactor : ℝ :=
    ((cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)).card : ℝ) *
      (Rweak ^ 10000 * (Ahead * rowMass) * ‖right‖)
  have hq :
      Summable fun headLength : ℕ => prefactor * q ^ headLength :=
    (summable_geometric_of_norm_lt_one hsmall).mul_left prefactor
  apply Summable.of_nonneg_of_le
    (fun headLength => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun headLength => ?_) hq
  classical
  rw [Fintype.sum_sigma]
  have hRweak0 : 0 ≤ Rweak := le_trans zero_le_one hRweak
  have hrowMass0 : 0 ≤ rowMass := by
    dsimp [rowMass]
    exact mul_nonneg (Nat.cast_nonneg _)
      (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)
  have hterm0 :
      0 ≤ Rweak ^ (10000 * (headLength + 1)) *
        (Ahead * rho ^ headLength * rowMass) * ‖right‖ :=
    mul_nonneg
      (mul_nonneg (pow_nonneg hRweak0 _)
        (mul_nonneg
          (mul_nonneg hAhead (pow_nonneg hrho _)) hrowMass0))
      (norm_nonneg _)
  calc
    ∑ head : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        ∑ tail : ↥(cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          head headLength),
          ‖cmp99SourcePi4ComplexFineHeadTailWordTerm
            anchor K hc hmass hK baseCoarseCovariance sigma
            (⟨head, tail⟩ :
              CMP99SourcePi4FineWalkIndex M Q R headLength)
            layerWord choice‖
        ≤
      ∑ head : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        ∑ _tail : ↥(cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          head headLength),
          Rweak ^ (10000 * (headLength + 1)) *
            (Ahead * rho ^ headLength * rowMass) * ‖right‖ := by
        apply Finset.sum_le_sum
        intro head _hhead
        apply Finset.sum_le_sum
        intro tail _htail
        simpa [rowMass, right, mul_assoc] using
          (norm_cmp99SourcePi4ComplexFineHeadTailWordTerm_le
            anchor K hc hmass hK baseCoarseCovariance
            hrate hgeom Cert hrange sigma hRweak hcap
            (⟨head, tail⟩ :
              CMP99SourcePi4FineWalkIndex M Q R headLength)
            layerWord choice)
    _ =
      ∑ head : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        ((cmp99AdmissibleTails
          (cmp99PhysicalPatchSuccessorSteps
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R)
          head headLength).card : ℝ) *
          (Rweak ^ (10000 * (headLength + 1)) *
            (Ahead * rho ^ headLength * rowMass) * ‖right‖) := by
        apply Finset.sum_congr rfl
        intro head _hhead
        simp
    _ ≤
      ∑ _head : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        ((branch ^ headLength : ℕ) : ℝ) *
          (Rweak ^ (10000 * (headLength + 1)) *
            (Ahead * rho ^ headLength * rowMass) * ‖right‖) := by
        apply Finset.sum_le_sum
        intro head _hhead
        apply mul_le_mul_of_nonneg_right _ hterm0
        exact_mod_cast
          (card_cmp99PhysicalPatchAdmissibleTails_le_pow_simpleDomainBound
            (cmp116CoarseFaceAdj 4 Q)
            (cmp99SourcePi4Charts :
              Finset (CMP99SourcePi4Chart Unit Q))
            (cmp99SourcePi4ChartCore (M := M))
            cmp99SourcePi4ChartEnlarged physicalBondDist R
            625 Δ hΔ hΔ1
            (fun chart => chart.1.domain)
            sourcePi4UnitDomain_injective_for_fine_head_absolute
            (fun left next hfollow =>
              cmp99SourcePi4ChartCanFollow_implies_domainsMeet
                (M := M) (Rrange := R) hrange
                left.1 next.1 hfollow)
            headLength head)
    _ = prefactor * q ^ headLength := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ, Fintype.card_coe]
      dsimp [prefactor, q, branch, rowMass, right,
        cmp116SourcePi4ComplexContourRatio,
        cmp116SourcePi4TerminalBranching]
      push_cast
      rw [pow_mul, pow_succ]
      ring

end

end YangMills.RG
