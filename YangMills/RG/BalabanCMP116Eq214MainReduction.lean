/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223PhysicalLocalizationProjector
import YangMills.RG.BalabanCMP116Eq223GaussianDomination

/-!
# CMP116 equation (2.14): main physical Gaussian reduction theorem

This module packages the formal reduction proved by the CMP116 campaign.  It
replaces the contour-dependent covariance-root matrix of finite Gaussian data
by the canonical matrix of a certified physical covariance root.  The shifted
Hessian is then positive automatically from the source half-smallness
`alpha5 * covNormBound < 1/2` and the canonical physical projector `P_Z0`.

The terminal theorems expose the two genuinely analytic obligations that
remain:

* `hdom`: the physical integrand is dominated almost everywhere by the real
  Gaussian produced by equations (2.20)--(2.23);
* `hmajorant`: the explicit determinant/source expression of (2.24) is bounded
  uniformly by the required contour weight.

No claim that these obligations, equation (2.26), or `hRpoly` are proved is
made here.
-/

namespace YangMills.RG

open MeasureTheory Matrix

namespace CMP116Eq214FiniteGaussianData

variable {d M N' Nc L lieDim nDelta nY : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
variable [NeZero Nc] [NeZero L] [NeZero lieDim]
variable {Ψ Φ E : Type*} [Norm E]

/-- Replace the Gaussian covariance root by the canonical matrix of a physical
root, leaving every other field of the literal equation-(2.14) data intact. -/
noncomputable def withPhysicalRootMatrix
    (G : CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Ψ Φ E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (root : PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
      PhysicalGaugeOneCochain d (M * N') Nc) :
    CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Ψ Φ E lieDim :=
  { G with covarianceRoot := fun _sigma _tau => Dict.physicalRootMatrix root }

@[simp] theorem withPhysicalRootMatrix_covarianceRoot
    (G : CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Ψ Φ E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (root : PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
      PhysicalGaugeOneCochain d (M * N') Nc)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ) :
    (G.withPhysicalRootMatrix Dict root).covarianceRoot sigma tau =
      Dict.physicalRootMatrix root := by
  rfl

/-- Pointwise main reduction: after the physical covariance and projector are
inserted, `hdom` and the explicit (2.24) bound are the only analytic estimates
needed to control the inner fluctuation integral. -/
theorem norm_innerIntegral_le_of_physicalGaussianReduction
    (G : CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Ψ Φ E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalGaugeOneCochain d (M * N') Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d (M * N') → PhysicalBond d (M * N') → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (Y0 P : Finset (Cube d L))
    (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (x : CMP116Eq214GaussianCoordinate (Cube d L) lieDim)
    (alpha5 innerGaussianBound : ℝ)
    (r : CMP116CoordIndex d L lieDim → ℝ)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hdom : ∀ᵐ b ∂matrixGaussianPi (Dict.physicalRootMatrix root),
      ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b‖ ≤
          cmp116Eq223RealGaussian
            (-(alpha5 • cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) r b)
    (hmajorant :
      cmp116Eq224GaussianMajorant (Dict.physicalRootMatrix root)
        (-(alpha5 • cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)))
        (fun i => (r i : ℂ)) ≤ innerGaussianBound) :
    ‖∫ b, (G.withPhysicalRootMatrix Dict root).toAnalyticData.innerIntegrand
        Y0 P sigma tau psi phi x b
        ∂(G.withPhysicalRootMatrix Dict root).toAnalyticData.conditionedMeasure
          sigma tau‖ ≤ innerGaussianBound := by
  let Gphys := G.withPhysicalRootMatrix Dict root
  have hpos :=
    Dict.posDef_physicalRootMatrix_of_alpha5_covariance_half_small_physicalZ0
      hcert Z0 alpha5 halpha5 hsmall
  have hpos' :
      (1 + (Dict.physicalRootMatrix root)ᵀ *
        (-(alpha5 • cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) *
        Dict.physicalRootMatrix root).PosDef := by
    simpa [sub_eq_add_neg] using hpos
  exact ((Gphys.norm_innerIntegral_le_eq224Majorant_of_domination
    Y0 P sigma tau psi phi x
    (-(alpha5 • cmp116Eq223CoordinateProjection
      (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) r
    (by simpa [Gphys] using hpos')
    (by simpa [Gphys] using hdom)).trans
      (by simpa [Gphys] using hmajorant))

/-- Main term theorem.  All covariance representation, norm transport,
localized-projector construction, Gaussian integrability, and shifted-Hessian
positivity are discharged internally.  The remaining substantive inputs are
the physical domination `hdom` and the uniform explicit-majorant estimate
`hmajorant`. -/
theorem norm_term_le_cauchyRate_of_physicalGaussianReduction
    (G : CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Ψ Φ E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalGaugeOneCochain d (M * N') Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d (M * N') → PhysicalBond d (M * N') → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (Y0 P : Finset (Cube d L))
    (Z0 : Finset (FinBox d N'))
    (psi : Ψ) (phi : Φ)
    (alpha5 outerBound innerGaussianBound : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hdom : ∀ sigma tau x,
      ∀ᵐ b ∂matrixGaussianPi (Dict.physicalRootMatrix root),
        ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.innerIntegrand
          Y0 P sigma tau psi phi x b‖ ≤
            cmp116Eq223RealGaussian
              (-(alpha5 • cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)))
              (r sigma tau x) b)
    (hmajorant : ∀ sigma tau x,
      cmp116Eq224GaussianMajorant (Dict.physicalRootMatrix root)
        (-(alpha5 • cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)))
        (fun i => (r sigma tau x i : ℂ)) ≤ innerGaussianBound) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound * innerGaussianBound)) := by
  let Gphys := G.withPhysicalRootMatrix Dict root
  apply Gphys.norm_term_le_cauchyRate_of_gaussianDomination
    Y0 P psi phi outerBound innerGaussianBound
    (fun _sigma _tau _x =>
      -(alpha5 • cmp116Eq223CoordinateProjection
        (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)))
    r hDelta hY houter_nonneg
  · simpa [Gphys] using houter
  · intro sigma tau x
    have hpos :=
      Dict.posDef_physicalRootMatrix_of_alpha5_covariance_half_small_physicalZ0
        hcert Z0 alpha5 halpha5 hsmall
    simpa [Gphys, sub_eq_add_neg] using hpos
  · simpa [Gphys] using hdom
  · simpa [Gphys] using hmajorant

end CMP116Eq214FiniteGaussianData
end YangMills.RG
