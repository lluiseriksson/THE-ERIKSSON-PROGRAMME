/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4MixedDerivativeDomainSeries

/-!
# Complete fixed-rate bound for a mixed connected-domain coefficient

Summing the length-layer estimate preserves the physical exponential kernel
rate.  The result is an explicit geometric prefactor multiplying the same
distance decay, with no dependence on the ambient volume.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The complete connected-domain coefficient inherits the fixed spatial
decay of every physical walk layer. -/
theorem norm_cmp116SourcePi4MixedDerivativeDomainCoefficient_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
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
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (S : Finset (FinBox 4 (2 * Q)))
    (root : FinBox 4 (2 * Q))
    (Y : Finset (FinBox 4 (2 * Q)))
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ‖cmp116SourcePi4MixedDerivativeDomainCoefficient
        (R := R) anchor K hc hmass hK sigma S root row col Y‖ ≤
      (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
        Real.exp (-(rate *
          (physicalBondDist row.1 col.1 : ℝ))) := by
  let layer := fun n : ℕ =>
    cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
      (R := R) (n := n) anchor K hc hmass hK
      sigma S root row col Y
  let spatial : ℝ :=
    Real.exp (-(rate *
      (physicalBondDist row.1 col.1 : ℝ)))
  have hlayer :
      Summable layer :=
    summable_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hRweak hcap S root Y row col hsmall
  have hmajor :
      HasSum
        (fun n : ℕ =>
          cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
            Δ Ahead rho Rweak n * spatial)
        ((cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
          (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
          spatial) :=
    (hasSum_cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
      Δ Ahead rho Rweak hsmall).mul_right spatial
  change ‖∑' n : ℕ, layer n‖ ≤ _
  calc
    ‖∑' n : ℕ, layer n‖ ≤ ∑' n : ℕ, ‖layer n‖ :=
      norm_tsum_le_tsum_norm hlayer.norm
    _ ≤ ∑' n : ℕ,
        cmp116SourcePi4MixedDerivativeDomainLayerAmplitude
          Δ Ahead rho Rweak n * spatial := by
      exact Summable.tsum_le_tsum
        (fun n =>
          norm_cmp116SourcePi4MixedDerivativeDomainLayerCoefficient_le'
            anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
            sigma hRweak hcap S root Y n row col)
        hlayer.norm hmajor.summable
    _ = (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
          (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
          spatial :=
      hmajor.tsum_eq

end

end YangMills.RG
