/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalBoundary
import YangMills.RG.BalabanCMP116Eq222CutoffSuppression

/-!
# The physical equation-(2.22) penalty in the equation-(2.26) boundary bound

The earlier Gaussian boundary theorem used the cutoff only as a contraction.
That loses the negative `|P|` exponent needed by the equation-(2.31)
resummation.  Here the literal equation-(2.22) estimate is composed before
either Cauchy family is extracted.  The localized determinant and outer
Gaussian moment are still evaluated internally, while the field-independent
residual and the large-field penalty remain as separate source factors.
-/

namespace YangMills.RG

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace CMP116Eq214FiniteGaussianData

variable {d M N' Nc L lieDim nDelta nY : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
variable [NeZero Nc] [NeZero L] [NeZero lieDim]
variable {Ψ Φ E : Type*} [Norm E]

/-- Fixed-contour physical Gaussian bound retaining the source `P` penalty.
The hypotheses `hinner` and `hinteraction` are the literal two parts used by
the equation-(2.22) producer; no bound on the already assembled integrand is
received. -/
theorem norm_analyticIntegrand_le_of_physicalCutoff_linearSource_expCard
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
    (alpha5 outerBound sourceRate gamma residual : ℝ)
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
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (houter : ∀ x, ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinner : ∀ x b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r x i * b i))
    (hinteraction : ∀ b,
      (G.interactionExponent sigma tau psi phi b).re +
          (gamma / 2) *
            (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          ((-(alpha5 • cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) *ᵥ b)) / 2) +
          residual)
    (hshape : ∀ x,
      r x = J *ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ‖J‖ ^ 2 ≤ sourceRate) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.analyticIntegrand
        Y0 P sigma tau psi phi‖ ≤
      outerBound *
        Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        Real.exp
          (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc (Dict.physicalRootMatrix root) alpha5
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
            (Z0.card : ℝ)) := by
  let Gphys := G.withPhysicalRootMatrix Dict root
  let S := Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0
  let A : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ :=
    -(alpha5 • cmp116Eq223CoordinateProjection S)
  let scale : ℝ :=
    Real.exp (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ))
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
  have hpos :=
    Dict.posDef_physicalRootMatrix_of_alpha5_covariance_half_small_physicalZ0
      hcert Z0 alpha5 halpha5 hsmall
  have hpos' :
      (1 + (Dict.physicalRootMatrix root)ᵀ * A *
        Dict.physicalRootMatrix root).PosDef := by
    simpa [A, S, sub_eq_add_neg] using hpos
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
  have hbase :
      ‖Gphys.toAnalyticData.analyticIntegrand
          Y0 P sigma tau psi phi‖ ≤
        (outerBound * scale *
          cmp116Eq225LocalizedSourceEnergyPrefactor S
            (Dict.physicalRootMatrix root) alpha5 0) *
          (Real.sqrt
            ((1 - 2 *
              (cmp116Eq225SourceCoefficient
                (Dict.physicalRootMatrix root) alpha5 * sourceRate)) ^
              S.card))⁻¹ := by
    unfold CMP116Eq214AnalyticData.analyticIntegrand
    rw [Gphys.toAnalyticData_mu0]
    unfold balabanCMP116Dmu0Flat
    apply norm_integral_le_of_localizedGaussianEnergy
      S (cmp116Eq225SourceCoefficient
        (Dict.physicalRootMatrix root) alpha5 * sourceRate)
      (outerBound * scale *
        cmp116Eq225LocalizedSourceEnergyPrefactor S
          (Dict.physicalRootMatrix root) alpha5 0) hbeta
    filter_upwards [] with x
    rw [norm_mul]
    have hinnerIntegral :=
      Gphys.norm_innerIntegral_le_exp_residual_sub_cardPenalty_mul_eq224Majorant
        Y0 P sigma tau psi phi x A (r x) gamma residual
        (by simpa [Gphys] using hgamma)
        (by simpa [Gphys] using hthreshold)
        (by simpa [Gphys] using hpos')
        (by simpa [Gphys] using hinner x)
        (by simpa [Gphys, A, S] using hinteraction)
    have hmajor :=
      cmp116Eq224_localized_gaussianMajorant_le_sourceEnergy_card
        S (Dict.physicalRootMatrix root) alpha5 (r x) x sourceRate 0
        halpha5 hmatrixSmall (hsource x)
    calc
      ‖Gphys.outerWeight sigma tau psi phi x‖ *
          ‖∫ b, Gphys.toAnalyticData.innerIntegrand
            Y0 P sigma tau psi phi x b
              ∂Gphys.toAnalyticData.conditionedMeasure sigma tau‖ ≤
        outerBound *
          (scale * cmp116Eq224GaussianMajorant
            (Dict.physicalRootMatrix root) A
            (fun i => ((r x) i : ℂ))) := by
              exact mul_le_mul (by simpa [Gphys] using houter x)
                (by simpa [Gphys, scale, A] using hinnerIntegral)
                (norm_nonneg _) houter_nonneg
      _ ≤ outerBound *
          (scale *
            (cmp116Eq225LocalizedSourceEnergyPrefactor S
              (Dict.physicalRootMatrix root) alpha5 0 *
            Real.exp
              ((cmp116Eq225SourceCoefficient
                (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
                ∑ i ∈ S, x i ^ 2))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by simpa [A] using hmajor)
              (Real.exp_nonneg _)) houter_nonneg
      _ = (outerBound * scale *
          cmp116Eq225LocalizedSourceEnergyPrefactor S
            (Dict.physicalRootMatrix root) alpha5 0) *
          Real.exp
            ((cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
              ∑ i ∈ S, x i ^ 2) := by ring
  have hcoefficient :
      0 ≤ cmp116Eq225SourceCoefficient
        (Dict.physicalRootMatrix root) alpha5 := by
    unfold cmp116Eq225SourceCoefficient
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (sub_pos.mpr hmatrixSmall).le)
  have hlocalized :=
    Dict.localizedGaussianProduct_le_exp_card_Z0 Z0
      (Dict.physicalRootMatrix root) alpha5
      (cmp116Eq225SourceCoefficient
        (Dict.physicalRootMatrix root) alpha5 * sourceRate)
      halpha5 hmatrixSmall
      (mul_nonneg hcoefficient hsourceRate)
      hbeta
  have hlocalized' :
      cmp116Eq225LocalizedSourceEnergyPrefactor S
          (Dict.physicalRootMatrix root) alpha5 0 *
        (Real.sqrt
          ((1 - 2 *
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate)) ^
            S.card))⁻¹ ≤
        Real.exp
          (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc (Dict.physicalRootMatrix root) alpha5
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
            (Z0.card : ℝ)) := by
    simpa [cmp116Eq225LocalizedSourceEnergyPrefactor, S] using hlocalized
  calc
    ‖Gphys.toAnalyticData.analyticIntegrand Y0 P sigma tau psi phi‖ ≤
        (outerBound * scale) *
          (cmp116Eq225LocalizedSourceEnergyPrefactor S
            (Dict.physicalRootMatrix root) alpha5 0 *
          (Real.sqrt
            ((1 - 2 *
              (cmp116Eq225SourceCoefficient
                (Dict.physicalRootMatrix root) alpha5 * sourceRate)) ^
              S.card))⁻¹) := by
        simpa [mul_assoc] using hbase
    _ ≤ (outerBound * scale) *
        Real.exp
          (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc (Dict.physicalRootMatrix root) alpha5
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
            (Z0.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hlocalized'
        (mul_nonneg houter_nonneg (Real.exp_nonneg _))
    _ = outerBound *
        Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        Real.exp
          (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc (Dict.physicalRootMatrix root) alpha5
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
            (Z0.card : ℝ)) := by
      rfl

/-- Uniform contour version of the preceding source-faithful cutoff bound. -/
theorem nestedCauchyBoundaryBound_of_physicalCutoff_linearSource_expCard
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
    (alpha5 outerBound sourceRate gamma residual : ℝ)
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
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinner : ∀ sigma tau x b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r sigma tau x i * b i))
    (hinteraction : ∀ sigma tau b,
      (G.interactionExponent sigma tau psi phi b).re +
          (gamma / 2) *
            (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          ((-(alpha5 • cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) *ᵥ b)) / 2) +
          residual)
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
      (outerBound *
        Real.exp
          (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
        Real.exp
          (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc (Dict.physicalRootMatrix root) alpha5
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
            (Z0.card : ℝ))) := by
  apply cmp116Eq214NestedCauchyBoundaryBound_of_forall_norm_le
  intro sigma tau
  exact G.norm_analyticIntegrand_le_of_physicalCutoff_linearSource_expCard
    Dict hcert Y0 P Z0 sigma tau psi phi alpha5 outerBound sourceRate
    gamma residual (r sigma tau) (J sigma tau) halpha5 hsmall
    hsourceRate hbeta houter_nonneg hgamma hthreshold
    (houter sigma tau) (hinner sigma tau) (hinteraction sigma tau)
    (hshape sigma tau) (hJ sigma tau)

/-- Fully source-normalized physical term bound retaining the equation-(2.22)
penalty.  Both contour families are consumed internally, so the conclusion is
already in the `D`-product times gap-factor form of equation (2.26). -/
theorem norm_term_le_of_physicalCutoff_eq226DomainGap
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
    (alpha5 outerBound sourceRate gamma residual : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (J : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    (domainMetric : Fin nY → ℕ) (gapL gapCard : ℕ)
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
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ G.threshold)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinner : ∀ sigma tau x b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r sigma tau x i * b i))
    (hinteraction : ∀ sigma tau b,
      (G.interactionExponent sigma tau psi phi b).re +
          (gamma / 2) *
            (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          ((-(alpha5 • cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) *ᵥ b)) / 2) +
          residual)
    (hshape : ∀ sigma tau x,
      r sigma tau x = J sigma tau *ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ∀ sigma tau, ‖J sigma tau‖ ^ 2 ≤ sourceRate) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      ((outerBound *
          Real.exp
            (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
          Real.exp
            (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
              M d Nc (Dict.physicalRootMatrix root) alpha5
              (cmp116Eq225SourceCoefficient
                (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
              (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Finset.univ) *
        cmp116Eq226GapFactor kappa1 gapL M gapCard := by
  let Gphys := G.withPhysicalRootMatrix Dict root
  let boundaryMajorant :=
    outerBound *
      Real.exp
        (residual - gamma / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
      Real.exp
        (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
          M d Nc (Dict.physicalRootMatrix root) alpha5
          (cmp116Eq225SourceCoefficient
            (Dict.physicalRootMatrix root) alpha5 * sourceRate) *
          (Z0.card : ℝ))
  apply Gphys.toAnalyticData.norm_term_le_eq226DomainGap_of_boundary
    Y0 P psi phi domainMetric gapL gapCard boundaryMajorant
  · simpa [Gphys] using hDeltaRadius
  · exact hnormalizedGap
  · simpa [Gphys] using hYRadius
  · exact hE0
  · exact hepsilon1
  · exact hC1
  · exact halpha4
  · exact hM
  · dsimp [boundaryMajorant]
    positivity
  · simpa [Gphys, boundaryMajorant] using
      (G.nestedCauchyBoundaryBound_of_physicalCutoff_linearSource_expCard
        Dict hcert Y0 P Z0 psi phi alpha5 outerBound sourceRate gamma residual
        r J halpha5 hsmall hsourceRate hbeta houter_nonneg hgamma hthreshold
        houter hinner hinteraction hshape hJ)

end CMP116Eq214FiniteGaussianData

end YangMills.RG
