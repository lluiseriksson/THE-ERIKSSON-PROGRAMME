/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214MainReduction
import YangMills.RG.BalabanCMP116Eq226SigmaCauchy

/-!
# The physical equation-(2.26) majorant before Cauchy extraction

The main Gaussian reduction previously delivered its strongest estimate only
after both Cauchy families had been applied.  This module exposes the same
physical calculation at the boundary-integrand level.  That is the level at
which the literal source radii from (2.18) and the ledger from (2.26) must be
matched; it avoids restating the desired post-Cauchy `termWeight` inequality.
-/

namespace YangMills.RG

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator

namespace CMP116Eq214FiniteGaussianData

variable {d M N' Nc L lieDim nDelta nY : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
variable [NeZero Nc] [NeZero L] [NeZero lieDim]
variable {Ψ Φ E : Type*} [Norm E]

/-- Fixed-contour physical Gaussian bound in polymer-volume form.  Both the
localized determinant and the outer Gaussian moment are evaluated internally;
the conclusion is about `analyticIntegrand`, before either Cauchy family. -/
theorem norm_analyticIntegrand_le_of_physicalGaussianReduction_linearSource_expCard
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
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N'))
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (alpha5 outerBound sourceRate : ℝ)
    (r : CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
      CMP116CoordIndex d L lieDim → ℝ)
    (J : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hsourceRate : 0 ≤ sourceRate)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        sourceRate) < 1)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ x, ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hdom : ∀ x,
      ∀ᵐ b ∂matrixGaussianPi (Dict.physicalRootMatrix root),
        ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.innerIntegrand
          Y0 P sigma tau psi phi x b‖ ≤
            cmp116Eq223RealGaussian
              (-(alpha5 • cmp116Eq223CoordinateProjection
                (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)))
              (r x) b)
    (hshape : ∀ x,
      r x = J *ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ‖J‖ ^ 2 ≤ sourceRate) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.analyticIntegrand
        Y0 P sigma tau psi phi‖ ≤
      outerBound * Real.exp
        (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
          M d Nc (Dict.physicalRootMatrix root) alpha5
          (cmp116Eq225SourceCoefficient
            (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
          (Z0.card : ℝ)) := by
  let S := Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0
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
  have hbeta0 :
      0 ≤ cmp116Eq225SourceCoefficient
        (Dict.physicalRootMatrix root) alpha5 * sourceRate := by
    unfold cmp116Eq225SourceCoefficient
    exact mul_nonneg
      (div_nonneg (sq_nonneg _)
        (mul_nonneg (by norm_num) (sub_pos.mpr hmatrixSmall).le))
      hsourceRate
  have hsource : ∀ x,
      (r x) ⬝ᵥ (r x) ≤ sourceRate * (∑ i ∈ S, x i ^ 2) + 0 := by
    intro x
    rw [hshape x]
    calc
      (J *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ⬝ᵥ
          (J *ᵥ (cmp116Eq223CoordinateProjection S *ᵥ x)) ≤
        ‖J‖ ^ 2 * ∑ i ∈ S, x i ^ 2 :=
          dotProduct_linearLocalizedSource_le S J x
      _ ≤ sourceRate * ∑ i ∈ S, x i ^ 2 :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = sourceRate * ∑ i ∈ S, x i ^ 2 + 0 := by ring
  have hbase :=
    (G.withPhysicalRootMatrix Dict root).norm_analyticIntegrand_le_of_sourceEnergy_card
      Y0 P sigma tau psi phi S alpha5 sourceRate 0 outerBound r
      halpha5 (by simpa using hmatrixSmall) (by simpa using hbeta)
      houter_nonneg (by simpa using houter) (by simpa using hdom) hsource
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _ houter_nonneg
  rw [cmp116Eq225LocalizedSourceEnergyPrefactor, mul_zero,
    Real.exp_zero, mul_one]
  exact Dict.localizedGaussianProduct_le_exp_card_Z0 Z0
    (Dict.physicalRootMatrix root) alpha5
    (cmp116Eq225SourceCoefficient
      (Dict.physicalRootMatrix root) alpha5 * sourceRate)
    halpha5 hmatrixSmall hbeta0 hbeta

/-- Uniform version of the preceding pointwise theorem, expressed as the
nested boundary predicate consumed by the literal Cauchy construction. -/
theorem nestedCauchyBoundaryBound_of_physicalGaussianReduction_linearSource_expCard
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
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N'))
    (psi : Ψ) (phi : Φ)
    (alpha5 outerBound sourceRate : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (J : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hsourceRate : 0 ≤ sourceRate)
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
      r sigma tau x = J sigma tau *ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ∀ sigma tau, ‖J sigma tau‖ ^ 2 ≤ sourceRate) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      G.deltaRadius G.yRadius
      (fun sigma tau =>
        (G.withPhysicalRootMatrix Dict root).toAnalyticData.analyticIntegrand
          Y0 P sigma tau psi phi)
      (outerBound * Real.exp
        (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
          M d Nc (Dict.physicalRootMatrix root) alpha5
          (cmp116Eq225SourceCoefficient
            (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
          (Z0.card : ℝ))) := by
  apply cmp116Eq214NestedCauchyBoundaryBound_of_forall_norm_le
  intro sigma tau
  exact G.norm_analyticIntegrand_le_of_physicalGaussianReduction_linearSource_expCard
    Dict hcert Y0 P Z0 sigma tau psi phi alpha5 outerBound sourceRate
    (r sigma tau) (J sigma tau) halpha5 hsmall hsourceRate hbeta
    houter_nonneg (houter sigma tau) (hdom sigma tau)
    (hshape sigma tau) (hJ sigma tau)

/-- Physical equation-(2.26) reduction with the complete inner `tau(Y)`
Cauchy family consumed by the literal source-domain product.  The remaining
outer Cauchy family is exposed unchanged. -/
theorem norm_term_le_deltaCauchyRate_of_physicalGaussianReduction_eq226DomainProduct
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
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N'))
    (psi : Ψ) (phi : Φ)
    (alpha5 outerBound sourceRate : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (J : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    (domainMetric : Fin nY → ℕ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hYRadius : G.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hsourceRate : 0 ≤ sourceRate)
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
      r sigma tau x = J sigma tau *ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ∀ sigma tau, ‖J sigma tau‖ ^ 2 ≤ sourceRate) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        ((outerBound * Real.exp
          (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc (Dict.physicalRootMatrix root) alpha5
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
            (Z0.card : ℝ))) *
          cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa domainMetric Finset.univ) := by
  let Gphys := G.withPhysicalRootMatrix Dict root
  apply Gphys.toAnalyticData.norm_term_le_deltaCauchyRate_mul_eq226DomainProduct
    Y0 P psi phi domainMetric
      (outerBound * Real.exp
        (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
          M d Nc (Dict.physicalRootMatrix root) alpha5
          (cmp116Eq225SourceCoefficient
            (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
          (Z0.card : ℝ)))
  · simpa [Gphys] using hDelta
  · simpa [Gphys] using hYRadius
  · exact hE0
  · exact hepsilon1
  · exact hC1
  · exact halpha4
  · exact hM
  · exact mul_nonneg houter_nonneg (Real.exp_nonneg _)
  · simpa [Gphys] using
      (G.nestedCauchyBoundaryBound_of_physicalGaussianReduction_linearSource_expCard
        Dict hcert Y0 P Z0 psi phi alpha5 outerBound sourceRate r J
        halpha5 hsmall hsourceRate hbeta houter_nonneg houter hdom hshape hJ)

/-- Source-normalized physical bound after both contour families have been
consumed.  The inner `tau(Y)` contours give the domain product of (2.26), and
the outer `sigma(Delta)` contours give its gap factor.  In particular no
post-Cauchy comparison and no independent positivity hypothesis for the
outer radii remain in the interface. -/
theorem norm_term_le_of_physicalGaussianReduction_eq226DomainGap
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
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N'))
    (psi : Ψ) (phi : Φ)
    (alpha5 outerBound sourceRate : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (J : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    (domainMetric : Fin nY → ℕ)
    (gapL gapCard : ℕ)
    (hDeltaRadius : G.deltaRadius =
      fun _ => cmp116Eq214SigmaCauchyRadius kappa1)
    (hnormalizedGap :
      ((((gapL * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
        (nDelta : ℝ))
    (hYRadius : G.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hsourceRate : 0 ≤ sourceRate)
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
      r sigma tau x = J sigma tau *ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ∀ sigma tau, ‖J sigma tau‖ ^ 2 ≤ sourceRate) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      ((outerBound * Real.exp
        (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
          M d Nc (Dict.physicalRootMatrix root) alpha5
          (cmp116Eq225SourceCoefficient
            (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
          (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Finset.univ) *
        cmp116Eq226GapFactor kappa1 gapL M gapCard := by
  have hDelta : ∀ i, 0 < G.deltaRadius i := by
    intro i
    rw [hDeltaRadius]
    exact cmp116Eq214SigmaCauchyRadius_pos kappa1
  have hbase :=
    G.norm_term_le_deltaCauchyRate_of_physicalGaussianReduction_eq226DomainProduct
      Dict hcert Y0 P Z0 psi phi alpha5 outerBound sourceRate r J
      domainMetric hDelta hYRadius hE0 hepsilon1 hC1 halpha4 hM
      halpha5 hsmall hsourceRate hbeta houter_nonneg houter hdom hshape hJ
  exact hbase.trans_eq
    (cmp116Eq214CauchyRate_eq_mul_gapFactor_of_deltaRadius
      G.deltaRadius kappa1
      ((outerBound * Real.exp
        (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
          M d Nc (Dict.physicalRootMatrix root) alpha5
          (cmp116Eq225SourceCoefficient
            (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
          (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Finset.univ)
      gapL M gapCard hDeltaRadius hnormalizedGap)

end CMP116Eq214FiniteGaussianData

end YangMills.RG
