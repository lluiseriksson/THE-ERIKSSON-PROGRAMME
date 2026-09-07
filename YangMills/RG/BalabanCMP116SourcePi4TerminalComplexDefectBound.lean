/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalComplexDefectLayer
import YangMills.RG.BalabanCMP116SourcePi4TerminalGroupedPhysicalWeightedRow
import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier
import YangMills.RG.PhysicalWeightedRowKernelMatrix

/-!
# Quantitative bound for one terminal complex contour-defect group

The weakening monomial contributes the contour radius and the literal
source-active budget `10000 * (n + 1)`.  The physical ordered product
contributes `Ahead * rho^n` with a fixed spatial rate, while reverse terminal
counting contributes only the local `Pi^4` branching power.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private theorem sourcePi4UnitDomain_injective_for_complex_defect
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

/-- Scalar amplitude of the complete length-`n` contour defect before the
fixed spatial exponential is inserted. -/
noncomputable def cmp116SourcePi4ComplexDefectLayerAmplitude
    (Δ : ℕ) (Ahead rho radius Rweak : ℝ) (n : ℕ) : ℝ :=
  (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
    (((10000 * (n + 1) : ℕ) : ℝ) * radius *
      Rweak ^ (10000 * (n + 1))) *
    (Ahead * rho ^ n)

/-- Entrywise fixed-rate bound for one terminal group of
`C_n(sigma) - C_n(1)`.  Every constant is local and independent of the
ambient number of source charts. -/
theorem norm_cmp116SourcePi4TerminalComplexDefectLayer_apply_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖cmp116SourcePi4TerminalComplexDefectLayer
        (R := R) anchor K hc hmass hK sigma n terminal row col‖ ≤
      (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
        (((10000 * (n + 1) : ℕ) : ℝ) * radius *
          Rweak ^ (10000 * (n + 1))) *
        ((Ahead * rho ^ n) *
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ)))) := by
  classical
  let walks := cmp99PhysicalPatchForwardTerminalWalks
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
    (cmp99SourcePi4ChartCore (M := M))
    cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal
  have hactive :
      ∀ chart : ↥(cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)),
        (cmp99SourceDomainLargeBlocks chart.1.domain ∩
          cmp116SourceSigmaZero anchor).card ≤ 10000 := by
    intro chart
    have hcard :=
      (cmp116SourceSigmaZeroPi4PhysicalChartDictionary
        (Label := Unit) anchor hrange).active_card_le chart
    simpa using hcard
  have hterm :
      ∀ walk ∈ walks,
        ‖(cmp116ComplexWeakeningMonomial
              (cmp116SourcePi4ForwardWalkActive anchor walk) sigma - 1) *
            cmp116ComplexPhysicalOperatorCoefficient
              (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
              col.1 row.1 col.2 row.2‖ ≤
          (((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1))) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ)))) := by
    intro walk hwalk
    have hmem :=
      (mem_cmp99PhysicalPatchForwardTerminalWalks_iff
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        (cmp99SourcePi4ChartCore (M := M))
        cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal walk).1 hwalk
    have hlen :=
      length_eq_of_mem_cmp99AdmissibleTails
        (cmp99PhysicalPatchSuccessorSteps
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (cmp99SourcePi4ChartCore (M := M))
          cmp99SourcePi4ChartEnlarged physicalBondDist R)
        hmem.1
    have hweighted :
        PhysicalCovarianceWeightedRowKernelBound
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
          physicalBondDist (Ahead * rho ^ n) rate := by
      rw [cmp116SourcePi4ForwardWalkOperator,
        cmp99PhysicalWalkTerm_eq_orderedProduct]
      simpa only [List.length_map, List.map_map, Function.comp_apply, hlen] using
        (Cert.orderedProduct_weightedRow htri walk.1
          (walk.2.map CMP99WalkStep.domain))
    have hExp :=
      physicalCovarianceExponentialKernelBound_of_weightedRow
        (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
        physicalBondDist hrate hweighted
    have hcoeff :
        ‖cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2‖ ≤
          (Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))) := by
      calc
        ‖cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2‖ ≤
            ‖cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk
              (singlePhysicalBondCochain col.1
                (EuclideanSpace.single col.2 (1 : ℝ))) row.1‖ :=
          norm_cmp116ComplexPhysicalOperatorCoefficient_le_targetValue
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2
        _ ≤ (Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ))) *
              ‖EuclideanSpace.single col.2 (1 : ℝ)‖ :=
          hExp.2.2 col.1 row.1
            (EuclideanSpace.single col.2 (1 : ℝ))
        _ = (Ahead * rho ^ n) *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ))) := by
          rw [EuclideanSpace.norm_single]
          simp
    have hmonomial :
        ‖cmp116ComplexWeakeningMonomial
            (cmp116SourcePi4ForwardWalkActive anchor walk) sigma - 1‖ ≤
          ((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1)) := by
      have hbase :=
        norm_cmp116ComplexWeakeningMonomial_walkActive_sub_one_le
          (⟨walk.1, walk.2⟩ :
            CMP99GeneralizedWalk Unit
              ↥(cmp99SourcePi4Charts :
                Finset (CMP99SourcePi4Chart Unit Q)))
          (fun chart =>
            cmp99SourceDomainLargeBlocks chart.1.domain ∩
              cmp116SourceSigmaZero anchor)
          10000 hactive sigma radius Rweak hradius hRweak
          (fun d _ => hdiff d) (fun d _ => hcap d)
      simpa only [cmp116SourcePi4ForwardWalkActive,
        CMP99GeneralizedWalk.length, hlen] using hbase
    rw [norm_mul]
    calc
      ‖cmp116ComplexWeakeningMonomial
          (cmp116SourcePi4ForwardWalkActive anchor walk) sigma - 1‖ *
          ‖cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2‖ ≤
          (((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1))) *
          ‖cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2‖ :=
        mul_le_mul_of_nonneg_right hmonomial (norm_nonneg _)
      _ ≤ (((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1))) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hcoeff
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) hradius)
            (pow_nonneg (le_trans zero_le_one hRweak) _))
  have hcard :
      walks.card ≤ (cmp116SourcePi4TerminalBranching Δ) ^ n := by
    dsimp [walks]
    change _ ≤ (625 * 626 * Δ ^ (2 * 625)) ^ n
    exact card_cmp99PhysicalPatchForwardTerminalWalks_le_pow_simpleDomainBound
      (cmp116CoarseFaceAdj 4 Q)
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      (cmp99SourcePi4ChartCore (M := M))
      cmp99SourcePi4ChartEnlarged physicalBondDist R 625 Δ
      hΔ hΔ1
      (fun chart => chart.1.domain)
      sourcePi4UnitDomain_injective_for_complex_defect
      (fun left right hfollow =>
        cmp99SourcePi4ChartCanFollow_implies_domainsMeet
          (M := M) (Rrange := R) hrange left.1 right.1 hfollow)
      n terminal
  have hcardReal :
      (walks.card : ℝ) ≤
        (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [cmp116SourcePi4TerminalComplexDefectLayer]
  change ‖∑ walk ∈ walks,
      (cmp116ComplexWeakeningMonomial
          (cmp116SourcePi4ForwardWalkActive anchor walk) sigma - 1) *
        cmp116ComplexPhysicalOperatorCoefficient
          (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
          col.1 row.1 col.2 row.2‖ ≤ _
  calc
    ‖∑ walk ∈ walks,
        (cmp116ComplexWeakeningMonomial
            (cmp116SourcePi4ForwardWalkActive anchor walk) sigma - 1) *
          cmp116ComplexPhysicalOperatorCoefficient
            (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
            col.1 row.1 col.2 row.2‖ ≤
        ∑ walk ∈ walks,
          ‖(cmp116ComplexWeakeningMonomial
              (cmp116SourcePi4ForwardWalkActive anchor walk) sigma - 1) *
            cmp116ComplexPhysicalOperatorCoefficient
              (cmp116SourcePi4ForwardWalkOperator K hc hmass hK walk)
              col.1 row.1 col.2 row.2‖ := norm_sum_le _ _
    _ ≤ ∑ _walk ∈ walks,
          (((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1))) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ)))) :=
      Finset.sum_le_sum fun walk hwalk => hterm walk hwalk
    _ = (walks.card : ℝ) *
          ((((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1))) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))))) := by
      simp
    _ ≤ (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
          ((((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1))) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))))) := by
      exact mul_le_mul_of_nonneg_right hcardReal
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) hradius)
            (pow_nonneg (le_trans zero_le_one hRweak) _))
          (mul_nonneg
            (mul_nonneg hAhead (pow_nonneg hrho n))
            (Real.exp_pos _).le))
    _ = (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
          (((10000 * (n + 1) : ℕ) : ℝ) * radius *
            Rweak ^ (10000 * (n + 1))) *
          ((Ahead * rho ^ n) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ)))) := by
      ring

/-- Exact source-core partitioning removes the terminal-chart count from the
complete length-`n` contour defect. -/
theorem norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖(cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma n -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) n) row col‖ ≤
      (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
        (((10000 * (n + 1) : ℕ) : ℝ) * radius *
          Rweak ^ (10000 * (n + 1))) *
        ((Ahead * rho ^ n) *
          Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ)))) := by
  classical
  obtain ⟨terminal, hterminal, hsource, hunique⟩ :=
    cmp99SourcePi4UnitChartCore_corePartition col.1
  let selected : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q)) := ⟨terminal, hterminal⟩
  have hterminalSum :
      (∑ next : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        cmp116SourcePi4TerminalComplexDefectLayer
          (R := R) anchor K hc hmass hK sigma n next row col) =
        cmp116SourcePi4TerminalComplexDefectLayer
          (R := R) anchor K hc hmass hK sigma n selected row col := by
    rw [Finset.sum_eq_single selected]
    · intro other _hother hne
      apply
        cmp116SourcePi4TerminalComplexDefectLayer_apply_eq_zero_of_not_mem_core
          (R := R) anchor K hc hmass hK sigma n other row col
      intro hotherSource
      apply hne
      exact Subtype.ext (hunique other.1 other.2 hotherSource)
    · intro hnot
      exact (hnot (Finset.mem_univ selected)).elim
  have hreconstruct :
      (∑ next : ↥(cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q)),
        cmp116SourcePi4TerminalComplexDefectLayer
          (R := R) anchor K hc hmass hK sigma n next row col) =
        (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK sigma n -
          cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK (fun _ => 1) n) row col := by
    simpa only [Matrix.sum_apply] using
      congrFun
        (congrFun
          (sum_cmp116SourcePi4TerminalComplexDefectLayer
            (R := R) anchor K hc hmass hK sigma n)
          row)
        col
  rw [← hreconstruct, hterminalSum]
  exact
    norm_cmp116SourcePi4TerminalComplexDefectLayer_apply_le
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap n selected row col

/-- The complete layer bound in named-amplitude form. -/
theorem norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le'
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (n : ℕ)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc) :
    ‖(cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma n -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) n) row col‖ ≤
      cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho radius Rweak n *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
  simpa [cmp116SourcePi4ComplexDefectLayerAmplitude, mul_assoc] using
    norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap n row col

/-- Volume-uniform matrix `L∞` bound for the complete length-`n` contour
defect. -/
theorem linfty_opNorm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (n : ℕ) :
    ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma n -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) n‖ ≤
      cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho radius Rweak n *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum 4 rate) := by
  apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
  · unfold cmp116SourcePi4ComplexDefectLayerAmplitude
    positivity
  · exact hgeom
  · intro row col
    exact
      norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le'
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        sigma hradius hRweak hdiff hcap n row col

end

end YangMills.RG
