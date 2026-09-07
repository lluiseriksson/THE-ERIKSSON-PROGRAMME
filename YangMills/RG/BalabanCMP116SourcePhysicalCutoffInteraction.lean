/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePhysicalAEInteraction

/-!
# Physical interaction absorption on conditioned cutoff support

The conditioned Gaussian is carried almost everywhere by the physical
localized coordinates, while the cubic potential estimate is available only
where the literal small-field cutoff is nonzero.  This module intersects
those two facts without strengthening either one to every ambient coordinate.

The quantitative covariance-lower certificate is an acceptance guard: it
prevents the almost-everywhere obligation from being made vacuous by choosing
the zero Gaussian root.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

/-- A cutoff-supported estimate for the literal physical potential, the
conditioned covariance carrier, and the physical bilateral `R2` bound produce
the source-faithful almost-everywhere interaction estimate. -/
theorem ae_interactionExponent_le_sourcePhysicalAlpha5_of_potential_cutoffSupport
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi
        (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Y0 : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N'))
    (P : Finset (PhysicalBond d (M * N')))
    (threshold : ℝ)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (conditionedCovariance :
      Matrix (PhysicalGaugeCoordIndex d (M * N') Nc)
        (PhysicalGaugeCoordIndex d (M * N') Nc) ℝ)
    (hroot :
      MatrixConditionedGaussianRootCertificate
        conditionedCovariance C.referenceRoot
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    (hnondegenerate :
      MatrixConditionedGaussianCovarianceLowerCertificate
        conditionedCovariance
        (cmp116SourcePhysicalLocalizedCoordinates Dict Z0))
    {potentialRate r2Rate gamma alpha residual : ℝ}
    (hpotential :
      let Csource := C.withSourcePhysicalBondField threshold
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
              Y0 P b ≠ 0 →
          (Csource.potential sigma tau psi phi b).re ≤
            potentialRate / 2 *
                (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
                  b ba ^ 2) +
              residual)
    (hR2 :
      (‖C.r2Matrix sigma tau psi phi‖ +
        ‖(C.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate)
    (hgamma : 0 ≤ gamma)
    (hbudget : potentialRate + r2Rate + gamma ≤ alpha) :
    let Csource := C.withSourcePhysicalBondField threshold
    ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
      Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
          Y0 P b ≠ 0 →
      (Csource.toLocalFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        gamma / 2 *
          (∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2) ≤
        alpha / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2) +
          residual := by
  dsimp only
  let Csource := C.withSourcePhysicalBondField threshold
  let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  have hcutoff :
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        (∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2) ≤
          ∑ ba ∈ S, b ba ^ 2 := by
    filter_upwards [hroot.ae_supported] with b hb
    calc
      (∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2) =
          ∑ bond ∈ P,
            ‖cmp116SourcePhysicalCoordinateCochain b bond‖ ^ 2 := by
              rfl
      _ ≤ ∑ ba, b ba ^ 2 :=
        sum_norm_sq_cmp116SourcePhysicalCoordinateCochain_le P b
      _ = ∑ ba ∈ S, b ba ^ 2 := hb.sum_sq_eq_sum_mem
  have hpotential' :
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        Csource.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
            Y0 P b ≠ 0 →
        (Csource.potential sigma tau psi phi b).re ≤
          potentialRate / 2 * (∑ ba ∈ S, b ba ^ 2) + residual := by
    simpa [Csource, S] using hpotential
  have hR2' :
      (‖Csource.r2Matrix sigma tau psi phi‖ +
        ‖(Csource.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate := by
    simpa [Csource] using hR2
  filter_upwards [hroot.ae_supported, hpotential', hcutoff] with b hb hp hc
  intro hcutoffSupport
  have hcombined :=
    cmp116Eq220_eq221_eq222_complexInteraction_le_localized
      (Csource.r2Matrix sigma tau psi phi) b
      (Csource.potential sigma tau psi phi b)
      (∑ ba ∈ S, b ba ^ 2)
      (∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2)
      potentialRate r2Rate gamma alpha residual
      (hp hcutoffSupport) hR2' hb.sum_sq_eq_sum_mem hc hgamma hbudget
  simpa [Csource, S] using hcombined

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
