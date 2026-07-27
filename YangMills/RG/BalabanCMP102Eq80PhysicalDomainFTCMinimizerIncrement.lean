/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalWordFTCInterchange
import YangMills.RG.BalabanCMP102Eq80PhysicalMinimizerDomainLocalization

/-!
# Fully domain-indexed nonlinear minimizer increment

One outer nonlinear minimizer increment is represented as an absolutely
convergent sum over coarse words, each followed by the finite sum of its
literal physical-domain FTC contributions.  The equality with the
nonlinear equation-(80) increment uses the proved `tsum`/integral
interchange.
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

/-- One nonlinear minimizer increment as the `tsum` of its complete
physical-domain FTC contributions. -/
noncomputable def cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement
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
  ∑' layerWord : Fin neumannLength → ℕ,
    ∑ Y : Finset (FinBox 4 (2 * Q)),
      cmp102Eq80PhysicalLayerWordDomainFTCContribution
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord D D₃ V₀ Hprefix (term neumannLength)
        Δπ J A' Y

/-- The literal nonlinear increment of one outer Neumann layer is exactly
its fully domain-indexed FTC `tsum`. -/
theorem
    cmp102Eq80MinimizerIncrement_eq_sourcePi4PhysicalDomainFTC
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
      cmp102Eq80SourcePi4PhysicalDomainFTCMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma neumannLength D D₃ V₀ Δπ J A' := by
  dsimp only
  rw [cmp102Eq80MinimizerIncrement_eq_integral_directionalDerivative
    D D₃ V₀
    (cmp102Eq80MinimizerPartialSum
      (fun i : ℕ =>
        cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK baseCoarseCovariance sigma i)
      neumannLength)
    (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
      (R := R) anchor K hc hmass hK baseCoarseCovariance
      sigma neumannLength)
    Δπ J A' hV₀]
  exact
    (tsum_cmp102Eq80PhysicalLayerWordDomainFTCContribution_eq_integral_neumannLayer
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall neumannLength
      D D₃ V₀
      (cmp102Eq80MinimizerPartialSum
        (fun i : ℕ =>
          cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
            (R := R) anchor K hc hmass hK baseCoarseCovariance sigma i)
        neumannLength)
      (cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK baseCoarseCovariance
        sigma neumannLength)
      Δπ J A' hV₀).symm

end

end YangMills.RG
