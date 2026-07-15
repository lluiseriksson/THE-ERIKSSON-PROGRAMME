/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq223PhysicalLocalizationProjector
import YangMills.RG.BalabanCMP116Eq223GaussianDomination
import YangMills.RG.BalabanCMP116Eq224SourceBound
import YangMills.RG.BalabanCMP116Eq225SourceEnergy
import YangMills.RG.BalabanCMP116Eq225LinearSource

/-!
# CMP116 equation (2.14): main physical Gaussian reduction theorem

This module packages the formal reduction proved by the CMP116 campaign.  It
replaces the contour-dependent covariance-root matrix of finite Gaussian data
by the canonical matrix of a certified physical covariance root.  The shifted
Hessian is then positive automatically from the source half-smallness
`alpha5 * covNormBound < 1/2` and the canonical physical projector `P_Z0`.

The strongest terminal theorem exposes the genuinely analytic obligations
that remain:

* `hdom`: the physical integrand is dominated almost everywhere by the real
  Gaussian produced by equations (2.20)--(2.23);
* an outer-field energy bound for the concrete physical source.

The determinant and inverse-source estimate of (2.24), and the exact outer
Gaussian moment of (2.25), are then produced internally.  Earlier, more
general endpoints retaining an explicit `hmajorant` or uniform source-norm
premise remain available for reuse.

No claim that the concrete kernel/source bounds, equation (2.26), or `hRpoly`
are proved is made here.
-/

namespace YangMills.RG

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator

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

/-- Strengthened terminal reduction with no `hmajorant` premise.  A uniform
Euclidean source-norm certificate is converted internally into the explicit
determinant/completed-square bound of (2.24).  Thus the public analytic
frontier is the physical domination estimate together with a scalar source
norm bound. -/
theorem norm_term_le_cauchyRate_of_physicalGaussianReduction_sourceNorm
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
    (alpha5 outerBound sourceNormBound : ℝ)
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
    (hsource : ∀ sigma tau x,
      (r sigma tau x) ⬝ᵥ (r sigma tau x) ≤ sourceNormBound) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound * cmp116Eq224SourceNormMajorant
            (Dict.physicalRootMatrix root) alpha5 sourceNormBound)) := by
  apply G.norm_term_le_cauchyRate_of_physicalGaussianReduction
    Dict hcert Y0 P Z0 psi phi alpha5 outerBound
      (cmp116Eq224SourceNormMajorant
        (Dict.physicalRootMatrix root) alpha5 sourceNormBound)
      r hDelta hY halpha5 hsmall houter_nonneg houter hdom
  intro sigma tau x
  have hmatrixSq :
      ‖Dict.physicalRootMatrix root‖ ^ 2 ≤ covNormBound := by
    rw [Dict.norm_physicalRootMatrix_sq_eq_covariance hcert]
    exact hcert.covariance_certificate.covariance_norm_bound
  have hmatrixSmall : alpha5 * ‖Dict.physicalRootMatrix root‖ ^ 2 < 1 := by
    calc
      alpha5 * ‖Dict.physicalRootMatrix root‖ ^ 2 ≤
          alpha5 * covNormBound :=
        mul_le_mul_of_nonneg_left hmatrixSq halpha5
      _ < (1 : ℝ) / 2 := hsmall
      _ < 1 := by norm_num
  exact cmp116Eq224_localized_gaussianMajorant_le_of_sourceNorm
    (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)
    (Dict.physicalRootMatrix root) alpha5 (r sigma tau x)
    sourceNormBound halpha5 hmatrixSmall (hsource sigma tau x)

/-- Strongest terminal reduction: the source may grow linearly with the outer
Gaussian field.  A localized source-energy estimate is propagated through
the completed-square bound of (2.24), and the resulting outer quadratic
exponential is integrated exactly as in (2.25).  No uniform-in-field source
norm or `hmajorant` premise remains. -/
theorem norm_term_le_cauchyRate_of_physicalGaussianReduction_sourceEnergy
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
    (alpha5 outerBound sourceRate sourceResidual : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        sourceRate) < 1)
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
    (hsource : ∀ sigma tau x,
      (r sigma tau x) ⬝ᵥ (r sigma tau x) ≤
        sourceRate *
          (∑ i ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0, x i ^ 2) +
        sourceResidual) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound *
            (cmp116Eq225SourceEnergyPrefactor
              (Dict.physicalRootMatrix root) alpha5 sourceResidual *
            (Real.sqrt
              ((1 - 2 *
                (cmp116Eq225SourceCoefficient
                  (Dict.physicalRootMatrix root) alpha5 * sourceRate)) ^
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹))) := by
  let Gphys := G.withPhysicalRootMatrix Dict root
  have hmatrixSq : ‖Dict.physicalRootMatrix root‖ ^ 2 ≤ covNormBound := by
    rw [Dict.norm_physicalRootMatrix_sq_eq_covariance hcert]
    exact hcert.covariance_certificate.covariance_norm_bound
  have hmatrixSmall : alpha5 * ‖Dict.physicalRootMatrix root‖ ^ 2 < 1 := by
    calc
      alpha5 * ‖Dict.physicalRootMatrix root‖ ^ 2 ≤ alpha5 * covNormBound :=
        mul_le_mul_of_nonneg_left hmatrixSq halpha5
      _ < (1 : ℝ) / 2 := hsmall
      _ < 1 := by norm_num
  apply Gphys.toAnalyticData.norm_term_le_cauchyRate
    Y0 P psi phi
      (outerBound *
        (cmp116Eq225SourceEnergyPrefactor
          (Dict.physicalRootMatrix root) alpha5 sourceResidual *
        (Real.sqrt
          ((1 - 2 *
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate)) ^
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹))
    hDelta hY
  apply cmp116Eq214NestedCauchyBoundaryBound_of_forall_norm_le
  intro sigma tau
  simpa [Gphys] using
    (Gphys.norm_analyticIntegrand_le_of_sourceEnergy
      Y0 P sigma tau psi phi
      (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)
      alpha5 sourceRate sourceResidual outerBound (r sigma tau)
      halpha5 (by simpa [Gphys] using hmatrixSmall)
      (by simpa [Gphys] using hbeta) houter_nonneg
      (by simpa [Gphys] using houter sigma tau)
      (by simpa [Gphys] using hdom sigma tau)
      (hsource sigma tau))

/-- Linear-source specialization of the (2.25) endpoint.  Once the concrete
source is represented as `J (P_Z0 X)`, only a uniform squared operator-norm
bound for `J` is needed to produce the outer source-energy estimate. -/
theorem norm_term_le_cauchyRate_of_physicalGaussianReduction_linearSource
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
    (alpha5 outerBound sourceRate : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (J : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        sourceRate) < 1)
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
    (hshape : ∀ sigma tau x,
      r sigma tau x =
        J sigma tau *ᵥ
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ∀ sigma tau, ‖J sigma tau‖ ^ 2 ≤ sourceRate) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound *
            (cmp116Eq225SourceEnergyPrefactor
              (Dict.physicalRootMatrix root) alpha5 0 *
            (Real.sqrt
              ((1 - 2 *
                (cmp116Eq225SourceCoefficient
                  (Dict.physicalRootMatrix root) alpha5 * sourceRate)) ^
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0).card))⁻¹))) := by
  apply G.norm_term_le_cauchyRate_of_physicalGaussianReduction_sourceEnergy
    Dict hcert Y0 P Z0 psi phi alpha5 outerBound sourceRate 0 r
    hDelta hY halpha5 hsmall hbeta houter_nonneg houter hdom
  intro sigma tau x
  rw [hshape sigma tau x]
  let S := Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0
  calc
    (J sigma tau *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ⬝ᵥ
        (J sigma tau *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ≤
      ‖J sigma tau‖ ^ 2 * ∑ i ∈ S, x i ^ 2 :=
        dotProduct_linearLocalizedSource_le S (J sigma tau) x
    _ ≤ sourceRate * ∑ i ∈ S, x i ^ 2 := by
      exact mul_le_mul_of_nonneg_right (hJ sigma tau) (by positivity)
    _ = sourceRate * ∑ i ∈ S, x i ^ 2 + 0 := by ring

end CMP116Eq214FiniteGaussianData
end YangMills.RG
