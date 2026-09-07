/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalMinimizerLocalizedTelescoping
import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailDomainReassembly

/-!
# Complete physical-domain localization of the nonlinear minimizer increment

The ordered outer Neumann increment and its FTC integral are left untouched.
Inside the directional derivative, every dependent coarse/fine choice is
replaced by the finite sum of its complete, absolutely convergent physical
domain coefficients.  Thus no infinite series is moved through the nonlinear
potential or through the FTC integral.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- One nonlinear outer minimizer increment, with every literal
coarse/fine choice already reassembled into its complete physical-domain
coefficients. -/
noncomputable def
    cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (neumannLength : ℕ)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A' : FineField M Q Nc) : ℝ :=
  let term := fun i : ℕ =>
    cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
      (R := R) anchor K hc hmass hK baseCoarseCovariance sigma i
  let Hprefix := cmp102Eq80MinimizerPartialSum term neumannLength
  ∫ t in (0 : ℝ)..1,
    ∑' layerWord : Fin neumannLength → ℕ,
      ∑ choice :
          CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord,
        ∑ Y : Finset (FinBox 4 (2 * Q)),
          cmp102Eq80PhysicalFineHeadTailDomainCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃
            (Hprefix + t • term neumannLength)
            Δπ J A'
            (fderiv ℝ V₀
              (A' - (Hprefix + t • term neumannLength) (D A')))
            Y

/-- The previous carrier-anchored nonlinear increment is exactly its
finite physical-domain reassembly.  Only finite choice/domain sums are
changed inside each fixed outer word; the FTC integral and outer `tsum`
retain their source order. -/
theorem
    cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement_eq_domainLocalized
    {M Q Nc R Δ : ℕ}
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
    (neumannLength : ℕ)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A' : FineField M Q Nc) :
    cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma neumannLength D D₃ V₀ Δπ J A' =
      cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma neumannLength D D₃ V₀ Δπ J A' := by
  unfold cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement
    cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
  dsimp only
  apply intervalIntegral.integral_congr
  intro t _ht
  apply tsum_congr
  intro layerWord
  apply Finset.sum_congr rfl
  intro choice _hchoice
  exact
    cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries_eq_sum_domainCoefficients
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice D D₃
      (cmp102Eq80MinimizerPartialSum
        (fun i : ℕ =>
          cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
            (R := R) anchor K hc hmass hK
            baseCoarseCovariance sigma i)
        neumannLength +
        t •
          cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
            (R := R) anchor K hc hmass hK
            baseCoarseCovariance sigma neumannLength)
      Δπ J A'
      (fderiv ℝ V₀
        (A' -
          (cmp102Eq80MinimizerPartialSum
              (fun i : ℕ =>
                cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
                  (R := R) anchor K hc hmass hK
                  baseCoarseCovariance sigma i)
              neumannLength +
            t •
              cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
                (R := R) anchor K hc hmass hK
                baseCoarseCovariance sigma neumannLength)
            (D A')))

/-- The literal nonlinear increment of one physical outer Neumann layer is
exactly the FTC integral of the complete physical-domain coefficients. -/
theorem
    cmp102Eq80MinimizerIncrement_eq_sourcePi4PhysicalDomainLocalized
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
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
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (neumannLength : ℕ)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A' : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    let term := fun i : ℕ =>
      cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma i
    cmp102Eq80MinimizerIncrement D D₃ V₀
        (cmp102Eq80MinimizerPartialSum term neumannLength)
        (term neumannLength) Δπ J A' =
      cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma neumannLength D D₃ V₀ Δπ J A' := by
  dsimp only
  calc
    cmp102Eq80MinimizerIncrement D D₃ V₀
        (cmp102Eq80MinimizerPartialSum
          (fun i : ℕ =>
            cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
              (R := R) anchor K hc hmass hK
              baseCoarseCovariance sigma i)
          neumannLength)
        (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma neumannLength)
        Δπ J A' =
      cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma neumannLength D D₃ V₀ Δπ J A' :=
      cmp102Eq80MinimizerIncrement_eq_sourcePi4PhysicalLocalized
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
        sigma hradius hRweak hdiff hcap hsmall neumannLength
        D D₃ V₀ Δπ J A' hV₀
    _ =
      cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma neumannLength D D₃ V₀ Δπ J A' :=
      cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement_eq_domainLocalized
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmall neumannLength
        D D₃ V₀ Δπ J A'

/-- Ordered finite sums of the complete physical-domain increments converge
to the literal equation-(80) potential at the fully reconstructed minimizer.
This is a convergence statement for the source order; no nonlinear
reordering is asserted. -/
theorem
    tendsto_sum_cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrements
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
    (J A' : FineField M Q Nc)
    (hV₀ : ContDiff ℝ 1 V₀) :
    Filter.Tendsto
      (fun n =>
        ∑ i ∈ Finset.range n,
          cmp102Eq80SourcePi4PhysicalDomainLocalizedMinimizerIncrement
            (R := R) anchor K hc hmass hK
            (cmp99SourcePi4WeakenedCoarseCovariance
              (R := R) anchor K hc hmass hK (fun _ => 1)
              hcoarseRate hcoarse)
            sigma i D D₃ V₀ Δπ J A')
      Filter.atTop
      (nhds
        (cmp102Eq80GlobalPotential D D₃ V₀
            (cmp99SourcePi4PhysicalFullBackgroundMinimizer
              (R := R) anchor K hc hmass hK sigma)
            Δπ J A' -
          cmp102Eq80GlobalPotential D D₃ V₀ 0 Δπ J A')) := by
  have htend :=
    tendsto_sum_cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrements
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      sigma hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
      D D₃ V₀ Δπ J A' hV₀
  convert htend using 1
  funext n
  apply Finset.sum_congr rfl
  intro i _hi
  exact
    (cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement_eq_domainLocalized
      anchor K hc hmass hK
      (cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse)
      hAhead hrho hrate hgeom Cert hsourceRange hΔ hΔ1
      sigma hRweak hcap hcontourSmall i
      D D₃ V₀ Δπ J A').symm

end

end YangMills.RG
