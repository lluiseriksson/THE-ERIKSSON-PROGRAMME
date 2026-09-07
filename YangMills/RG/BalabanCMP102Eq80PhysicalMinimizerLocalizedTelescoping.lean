/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80MinimizerTelescoping
import YangMills.RG.BalabanCMP102Eq80PhysicalFineHeadTailAnchoredLocalization

/-!
# Physical localized telescoping of CMP102 equation (80)

The complete CMP99 background minimizer is an ordered outer Neumann
series.  Since the equation-(80) potential is nonlinear in that
minimizer, its terms cannot be passed independently through the
potential.  This module keeps the outer Neumann order, applies the exact
FTC identity to each nonlinear increment, and only then expands the
directional derivative into the literal physical head-tail words,
grouped by their canonical `Pi^4`-anchored domains.

No infinite series are reordered.  The terminal convergence statement
is a `Tendsto` of ordered finite sums, not a `HasSum` assertion for the
nonlinear localized increments.
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

/-- One source-ordered nonlinear minimizer increment after replacing its
literal directional derivative by the exact `Pi^4`-anchored physical
word expansion. -/
noncomputable def cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement
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
        cmp102Eq80PhysicalChoiceAnchoredDerivativeSeries
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃
          (Hprefix + t • term neumannLength)
          Δπ J A'
          (fderiv ℝ V₀
            (A' - (Hprefix + t • term neumannLength) (D A')))

/-- The literal nonlinear increment of one physical outer Neumann layer
is exactly its localized physical word integral. -/
theorem
    cmp102Eq80MinimizerIncrement_eq_sourcePi4PhysicalLocalized
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
      cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement
        (R := R) anchor K hc hmass hK baseCoarseCovariance sigma neumannLength
        D D₃ V₀ Δπ J A' := by
  dsimp only
  rw [cmp102Eq80MinimizerIncrement_eq_integral_directionalDerivative
    D D₃ V₀ _ _ Δπ J A' hV₀]
  unfold cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement
  dsimp only
  apply intervalIntegral.integral_congr
  intro t _ht
  exact
    cmp102Eq80PropagatorDirectionalDerivative_physicalNeumannLayer_eq_tsum_localizedWords
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hsmall neumannLength
      D D₃
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

/-- The ordered finite sums of the localized physical increments converge
to the literal equation-(80) potential at the complete reconstructed
background minimizer.  This is the source-faithful nonlinear replacement
for an invalid termwise passage of the minimizer `tsum` through the
potential. -/
theorem
    tendsto_sum_cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrements
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
          cmp102Eq80SourcePi4PhysicalLocalizedMinimizerIncrement
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
  let baseCoarseCovariance :=
    cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor K hc hmass hK (fun _ => 1)
      hcoarseRate hcoarse
  let term := fun i : ℕ =>
    cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
      (R := R) anchor K hc hmass hK baseCoarseCovariance sigma i
  have hterm : Summable term := by
    exact
      summable_cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayers_of_source
        anchor K hsourceRange hc hmass hK hcoarseRate hcoarse
        hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        sigma hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
  have hfull :
      cmp99SourcePi4PhysicalFullBackgroundMinimizer
          (R := R) anchor K hc hmass hK sigma =
        ∑' i : ℕ, term i := by
    exact
      cmp99SourcePi4PhysicalFullBackgroundMinimizer_eq_tsum_neumannLayers_of_source
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        sigma hradius hRweak hdiff hcap hcontourSmall hcoarseSmall
  have htend :=
    tendsto_cmp102Eq80GlobalPotential_partialSum_increments
      D D₃ V₀ term Δπ J A' hV₀.continuous hterm
  rw [hfull]
  convert htend using 1
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  simpa [baseCoarseCovariance, term] using
    (cmp102Eq80MinimizerIncrement_eq_sourcePi4PhysicalLocalized
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hsourceRange hΔ hΔ1
      sigma hradius hRweak hdiff hcap hcontourSmall i
      D D₃ V₀ Δπ J A' hV₀).symm

end

end YangMills.RG
