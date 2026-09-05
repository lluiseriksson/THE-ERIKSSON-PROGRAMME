/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCSourceReassembly
import YangMills.RG.BalabanCMP102Eq80PhysicalMinimizerDomainLocalization

/-!
# Complete source-ordered reassembly of the physical-domain FTC series

The literal nonlinear equation-(80) potential is identified by the ordered
partial sums of its outer Neumann increments.  Each fixed increment is already
the finite sum of its physical-domain FTC coefficients, and the source metric
gives absolute summability in the outer length below every fixed domain.

This file combines those facts without applying an infinite Fubini theorem:
only the two finite sums in an ordered partial sum are commuted.  Uniqueness of
limits then identifies the physical potential difference with the finite sum
of the complete outer series below each domain.

No termwise identification with the separate recursive Faà di Bruno
connected-domain activities is asserted.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- One fixed outer Neumann coefficient is literally zero outside the
nonempty face-connected physical localization domains.  This is produced
from the support of every layer word; it is not a summability hypothesis. -/
theorem
    cmp102Eq80PhysicalNeumannDomainFTCContribution_eq_zero_of_not_localizationDomain
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
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : CoarseField Q Nc →L[ℝ] FineField M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hY : ¬(Y.Nonempty ∧
      walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y)) :
    cmp102Eq80PhysicalNeumannDomainFTCContribution
        (R := R) (n := n) anchor K hc hmass hK
        baseCoarseCovariance sigma D D₃ V₀ P T Δπ J A Y = 0 := by
  unfold cmp102Eq80PhysicalNeumannDomainFTCContribution
  calc
    (∑' layerWord : Fin n → ℕ,
      cmp102Eq80PhysicalLayerWordDomainFTCContribution
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma
        layerWord D D₃ V₀ P T Δπ J A Y) =
        ∑' _layerWord : Fin n → ℕ, 0 := by
      apply tsum_congr
      intro layerWord
      exact
        cmp102Eq80PhysicalLayerWordDomainFTCContribution_eq_zero_of_not_localizationDomain
          anchor K hc hmass hK baseCoarseCovariance sigma
          layerWord D D₃ V₀ P T Δπ J A Y hY
    _ = 0 := tsum_zero

set_option maxHeartbeats 8000000 in
/-- The literal equation-(80) potential difference at the fully reconstructed
physical minimizer is exactly the finite sum, over all physical domains, of
their complete outer Neumann FTC series.

All summability is generated from the source metric.  Nonempty
face-connected domains use the complete-domain source theorem, while every
other finite set vanishes term by term by physical support. -/
theorem
    cmp102Eq80SourcePi4PhysicalPotentialDifference_eq_sum_completeDomainFTC_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange
      K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀)
    {cardRatio metricRatio summationRatio κcard κmetric : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 ≤ κcard)
    (hκmetric : 0 ≤ κmetric)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M)
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse)
          Ahead rho rate Rweak ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp (-(κmetric * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (houterSmall :
      cmp102Eq80PhysicalOuterNeumannSourceMetricRatio
        (Q := Q) (Δ := Δ) summationRatio < 1) :
    let baseCoarseCovariance :=
      cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse
    let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
      fun neumannLength =>
        cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma neumannLength
    cmp102Eq80GlobalPotential D D₃ V₀
        (cmp99SourcePi4PhysicalFullBackgroundMinimizer
          (R := R) anchor K hc hmass hK sigma)
        Δπ J A -
      cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A =
      ∑ Y : Finset (FinBox 4 (2 * Q)),
        ∑' n : ℕ,
          cmp102Eq80PhysicalNeumannDomainFTCContribution
            (R := R) (n := n) anchor K hc hmass hK
            baseCoarseCovariance sigma D D₃ V₀
            (cmp102Eq80MinimizerPartialSum term n) (term n)
            Δπ J A Y := by
  classical
  let baseCoarseCovariance :=
    cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor K hc hmass hK (fun _ => 1)
      hcoarseRate hcoarse
  let term : ℕ → (CoarseField Q Nc →L[ℝ] FineField M Q Nc) :=
    fun neumannLength =>
      cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma neumannLength
  let outerTerm :
      ℕ → Finset (FinBox 4 (2 * Q)) → ℝ :=
    fun n Y =>
      cmp102Eq80PhysicalNeumannDomainFTCContribution
        (R := R) (n := n) anchor K hc hmass hK
        baseCoarseCovariance sigma D D₃ V₀
        (cmp102Eq80MinimizerPartialSum term n) (term n)
        Δπ J A Y
  have htend :=
    tendsto_sum_cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrements
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      sigma hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
      D D₃ V₀ Δπ J A hV₀
  have hterm (n : ℕ) :
      cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma n D D₃ V₀ Δπ J A =
        ∑ Y : Finset (FinBox 4 (2 * Q)), outerTerm n Y := by
    calc
      cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma n D D₃ V₀ Δπ J A =
        cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement
          (R := R) anchor K hc hmass hK baseCoarseCovariance
          sigma n D D₃ V₀ Δπ J A := by
            exact
              cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement_eq_domainFTC
                anchor K hc hmass hK baseCoarseCovariance
                hAhead hrho hrate hgeom Cert htri hsourceRange hΔ hΔ1
                sigma hradius hRweak hdiff hcap hcontourSmall n
                D D₃ V₀ Δπ J A hV₀
      _ = ∑ Y : Finset (FinBox 4 (2 * Q)), outerTerm n Y := by
            simpa [baseCoarseCovariance, term, outerTerm] using
              (cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement_eq_sum_neumannDomainFTC_of_source
                anchor K hsourceRange hc hmass hK hcoarseRate hcoarse
                hAhead hrho hrate hgeom Cert htri hΔ hΔ1 sigma
                hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
                D D₃ V₀ Δπ J A hV₀
                hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
                hsplit hcardDecay hmetricDecay hsmall n)
  have htendOrdered :
      Filter.Tendsto
        (fun N =>
          ∑ n ∈ Finset.range N,
            ∑ Y : Finset (FinBox 4 (2 * Q)), outerTerm n Y)
        Filter.atTop
        (nhds
          (cmp102Eq80GlobalPotential D D₃ V₀
              (cmp99SourcePi4PhysicalFullBackgroundMinimizer
                (R := R) anchor K hc hmass hK sigma)
              Δπ J A -
            cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A)) := by
    convert htend using 1
    funext N
    apply Finset.sum_congr rfl
    intro n _hn
    exact (hterm n).symm
  obtain ⟨C, hC0, hcomplete⟩ :=
    exists_uniform_bound_cmp102Eq80SourcePi4PhysicalCompleteDomainFTC
      anchor K hsourceRange hc hmass hK hcoarseRate hcoarse
      hAhead hrho hrate hgeom Cert htri hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
      D D₃ V₀ Δπ J A hV₀
      hcardRatio0 hmetricRatio0 hsummation0 hκcard hκmetric
      hsplit hcardDecay hmetricDecay hsmall houterSmall
  have hYtend (Y : Finset (FinBox 4 (2 * Q))) :
      Filter.Tendsto
        (fun N => ∑ n ∈ Finset.range N, outerTerm n Y)
        Filter.atTop
        (nhds (∑' n : ℕ, outerTerm n Y)) := by
    by_cases hY :
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 (2 * Q)) Y
    · let Yphys : CMP116LocalizationDomain M (2 * Q) :=
        { blocks := Y
          nonempty := hY.1
          connected := hY.2 }
      have hsummable : Summable (fun n : ℕ => outerTerm n Y) := by
        simpa [baseCoarseCovariance, term, outerTerm, Yphys] using
          (hcomplete Yphys).1
      exact hsummable.hasSum.tendsto_sum_nat
    · have hzero : ∀ n : ℕ, outerTerm n Y = 0 := by
        intro n
        exact
          cmp102Eq80PhysicalNeumannDomainFTCContribution_eq_zero_of_not_localizationDomain
            anchor K hc hmass hK baseCoarseCovariance sigma
            D D₃ V₀
            (cmp102Eq80MinimizerPartialSum term n) (term n)
            Δπ J A Y hY
      simpa [hzero] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _N : ℕ => (0 : ℝ))
            Filter.atTop (nhds 0))
  have htendDomains :
      Filter.Tendsto
        (fun N =>
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            ∑ n ∈ Finset.range N, outerTerm n Y)
        Filter.atTop
        (nhds
          (∑ Y : Finset (FinBox 4 (2 * Q)),
            ∑' n : ℕ, outerTerm n Y)) := by
    exact tendsto_finset_sum Finset.univ (fun Y _hY => hYtend Y)
  have htendOrdered' :
      Filter.Tendsto
        (fun N =>
          ∑ Y : Finset (FinBox 4 (2 * Q)),
            ∑ n ∈ Finset.range N, outerTerm n Y)
        Filter.atTop
        (nhds
          (cmp102Eq80GlobalPotential D D₃ V₀
              (cmp99SourcePi4PhysicalFullBackgroundMinimizer
                (R := R) anchor K hc hmass hK sigma)
              Δπ J A -
            cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A)) := by
    convert htendOrdered using 1
    funext N
    exact Finset.sum_comm
  have hunique :=
    tendsto_nhds_unique htendOrdered' htendDomains
  simpa [baseCoarseCovariance, term, outerTerm] using hunique

end

end YangMills.RG
