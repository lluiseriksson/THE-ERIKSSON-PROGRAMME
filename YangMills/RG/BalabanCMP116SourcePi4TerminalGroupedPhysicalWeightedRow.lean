/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalWalkFiniteSum
import YangMills.RG.BalabanCMP116SourcePi4TerminalGroupedWeightedRow
import YangMills.RG.BalabanCMP99PatchedParametrixWeightedWalk
import YangMills.RG.PhysicalWeightedRowKernelFiniteSum

/-!
# Physical weighted-row bound for one terminal source group

The factorwise physical certificate bounds every length-`n` walk by
`Ahead * rho^n`.  Exact terminal walk counting contributes only the local
lattice-animal branching power, never the ambient number of charts.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private theorem sourcePi4UnitDomain_injective
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

/-- The explicit local branching factor for source `Π⁴` charts. -/
def cmp116SourcePi4TerminalBranching (Δ : ℕ) : ℕ :=
  625 * 626 * Δ ^ (2 * 625)

/-- Complete volume-uniform weighted-row estimate for one terminal group.
The amplitude contains only the explicit local branching power. -/
theorem cmp116SourcePi4TerminalGroupedWalkLayer_weightedRow_physical
    {M Q Nc R Δ : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (dist : PhysicalBond 4 (M * (2 * Q)) →
      PhysicalBond 4 (M * (2 * Q)) → ℕ)
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 ≤ rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK dist Ahead rho rate)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (n : ℕ)
    (terminal : ↥(cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))) :
    PhysicalCovarianceWeightedRowKernelBound
      (cmp116SourcePi4TerminalGroupedWalkLayer
        (R := R) K hc hmass hK n terminal)
      dist
      ((((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
        (Ahead * rho ^ n))
      rate := by
  let walks := cmp99PhysicalPatchForwardTerminalWalks
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
    (cmp99SourcePi4ChartCore (M := M))
    cmp99SourcePi4ChartEnlarged physicalBondDist R n terminal
  have hfinite :
      PhysicalCovarianceWeightedRowKernelBound
        (cmp116SourcePi4TerminalWalkFiniteSum
          (R := R) K hc hmass hK n terminal)
        dist ((walks.card : ℝ) * (Ahead * rho ^ n)) rate := by
    apply physicalCovarianceWeightedRowKernelBound_finset_sum
      walks
      (cmp116SourcePi4ForwardWalkOperator K hc hmass hK)
      dist
      (mul_nonneg hAhead (pow_nonneg hrho n)) hrate
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
    rw [cmp116SourcePi4ForwardWalkOperator,
      cmp99PhysicalWalkTerm_eq_orderedProduct]
    simpa only [List.length_map, List.map_map, Function.comp_apply, hlen] using
      (Cert.orderedProduct_weightedRow htri walk.1
        (walk.2.map CMP99WalkStep.domain))
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
      sourcePi4UnitDomain_injective
      (fun left right hfollow =>
        cmp99SourcePi4ChartCanFollow_implies_domainsMeet
          (M := M) (Rrange := R) hrange left.1 right.1 hfollow)
      n terminal
  have hcardReal :
      (walks.card : ℝ) ≤
        (((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [← cmp116SourcePi4TerminalWalkFiniteSum_eq_groupedWalkLayer
    (R := R) K hc hmass hK n terminal]
  exact physicalCovarianceWeightedRowKernelBound_mono_amplitude
    hfinite
    (mul_le_mul_of_nonneg_right hcardReal
      (mul_nonneg hAhead (pow_nonneg hrho n)))

/-- The complete all-head generated layer has the same local branching
amplitude.  Exact source-core partitioning prevents a terminal-chart factor. -/
theorem cmp116SourcePi4QuotientGeneratedWalkLayer_weightedRow_physical
    {M Q Nc R Δ : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (dist : PhysicalBond 4 (M * (2 * Q)) →
      PhysicalBond 4 (M * (2 * Q)) → ℕ)
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 ≤ rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK dist Ahead rho rate)
    (htri : ∀ target source middle,
      dist target source ≤ dist target middle + dist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (n : ℕ) :
    PhysicalCovarianceWeightedRowKernelBound
      (cmp116SourcePi4QuotientGeneratedWalkLayer
        (R := R) K hc hmass hK n)
      dist
      ((((cmp116SourcePi4TerminalBranching Δ) ^ n : ℕ) : ℝ) *
        (Ahead * rho ^ n))
      rate := by
  apply cmp116SourcePi4QuotientGeneratedWalkLayer_weightedRow_of_terminalGroups
    K hc hmass hK n dist
  · positivity
  · exact hrate
  · intro terminal
    exact cmp116SourcePi4TerminalGroupedWalkLayer_weightedRow_physical
      K hc hmass hK dist hAhead hrho hrate Cert htri hrange hΔ hΔ1 n terminal

end

end YangMills.RG
