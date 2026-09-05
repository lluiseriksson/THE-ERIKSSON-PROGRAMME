/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourOuterEnergy
import YangMills.RG.BalabanCMP116Eq222CutoffSupportInteraction

/-!
# Cutoff-support physical contour boundary

The literal equation-(2.14) integrand vanishes when its cutoff factor
vanishes.  Hence the physical interaction estimate is required only on the
support of that factor.  This module connects that source-faithful interface
to the same outer-energy, localized-determinant, and outer-Gaussian boundary
used by the equation-(2.26) ledger.

No unrestricted estimate in the inner Gaussian variable is assumed or
derived.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 1000000 in
/-- The physical contour boundary with the interaction estimate required
only where the literal cutoff factor is nonzero. -/
theorem nestedCauchyBoundaryBound_of_outerInteractionEnergy_cutoffSupport_expCard
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary
      d (M * N') Nc d L lieDim)
    (Y0 P : Finset (Cube d L))
    (Z0 : Finset (FinBox d N'))
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (alpha sourceRate sourceResidual outerBound outerRate gamma residual : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖C.referenceRoot‖ ^ 2 < 1)
    (hsourceRate : 0 ≤ sourceRate)
    (houterRate : 0 ≤ outerRate)
    (hbeta :
      2 * (outerRate +
        cmp116Eq225SourceCoefficient C.referenceRoot alpha *
          sourceRate) < 1)
    (houter_nonneg : 0 ≤ outerBound)
    (hgamma : 0 ≤ gamma)
    (hthreshold : 0 ≤ C.threshold)
    (houter : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ x,
        ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.outerWeight
            sigma tau psi phi x‖ ≤
          outerBound *
            Real.exp (outerRate *
              ∑ i ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0,
                x i ^ 2))
    (hinner : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ x b,
        ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.innerWeight
            sigma tau psi phi x b‖ ≤
          Real.exp (∑ i, r sigma tau x i * b i))
    (hinteraction : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ b,
        C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
            Y0 P b ≠ 0 →
        (C.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
            sigma tau psi phi b).re +
          (gamma / 2) *
            (∑ e ∈ P,
              ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
                b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          Matrix.mulVec
            (-(alpha • cmp116Eq223CoordinateProjection
              (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) b) / 2) +
          residual)
    (hsource : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ x,
        (r sigma tau x) ⬝ᵥ (r sigma tau x) ≤
          sourceRate *
            (∑ i ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0,
              x i ^ 2) +
          sourceResidual) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      C.deltaRadius C.yRadius
      (fun sigma tau =>
        C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.analyticIntegrand
          Y0 P sigma tau psi phi)
      ((outerBound *
          Real.exp
            (residual - gamma / 2 * C.threshold ^ 2 * (P.card : ℝ))) *
        Real.exp
          (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceResidual +
            PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
              M d Nc C.referenceRoot alpha
                (outerRate +
                  cmp116Eq225SourceCoefficient C.referenceRoot alpha *
                    sourceRate) *
              (Z0.card : ℝ))) := by
  apply cmp116Eq214NestedCauchyBoundaryBound_of_shiftedPolydiscs
  intro sigma tau hsigma htau
  let S := Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0
  let beta :=
    outerRate +
      cmp116Eq225SourceCoefficient C.referenceRoot alpha * sourceRate
  let scale :=
    Real.exp
      (residual - gamma / 2 * C.threshold ^ 2 * (P.card : ℝ))
  let G := C.toLocalFiniteGaussianData.toFiniteGaussianData
  let A := -(alpha • cmp116Eq223CoordinateProjection S)
  have hfixed :
      G.covarianceRoot sigma tau = C.referenceRoot := rfl
  have hdom :
      ∀ x,
        ∀ᵐ b ∂matrixGaussianPi C.referenceRoot,
          ‖G.toAnalyticData.innerIntegrand
              Y0 P sigma tau psi phi x b‖ ≤
            scale * cmp116Eq223RealGaussian A (r sigma tau x) b := by
    intro x
    simpa [G, A, S, scale, hfixed] using
      (G.ae_norm_innerIntegrand_le_exp_residual_sub_cardPenalty_mul_realGaussian_of_cutoffSupport
        Y0 P sigma tau psi phi x A (r sigma tau x) gamma residual
        (by simpa [G] using hgamma)
        (by simpa [G] using hthreshold)
        (by simpa [G] using hinner sigma tau hsigma htau x)
        (by simpa [G, A, S] using
          hinteraction sigma tau hsigma htau))
  have hpoint :=
    G.norm_analyticIntegrand_le_of_outerInteractionEnergy_scaledInner
      Y0 P sigma tau psi phi S alpha sourceRate sourceResidual
      outerBound outerRate scale (r sigma tau)
      halpha
      (by simpa [hfixed] using hsmall)
      (by simpa [S, beta, hfixed] using hbeta)
      houter_nonneg (Real.exp_nonneg _)
      (by simpa [S] using houter sigma tau hsigma htau)
      (by simpa [G, A, hfixed] using hdom)
      (by simpa [S] using hsource sigma tau hsigma htau)
  have hcoeff :
      0 ≤ cmp116Eq225SourceCoefficient C.referenceRoot alpha := by
    unfold cmp116Eq225SourceCoefficient
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
  have hbeta0 : 0 ≤ beta := by
    unfold beta
    exact add_nonneg houterRate (mul_nonneg hcoeff hsourceRate)
  have hgaussian :=
    Dict.localizedGaussianProduct_le_exp_card_Z0 Z0
      C.referenceRoot alpha beta halpha hsmall hbeta0
      (by simpa [beta] using hbeta)
  have hfactor :
      cmp116Eq225LocalizedSourceEnergyPrefactor S
          C.referenceRoot alpha sourceResidual *
        (Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ ≤
      Real.exp
        (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
            sourceResidual +
          PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc C.referenceRoot alpha beta * (Z0.card : ℝ)) := by
    rw [cmp116Eq225LocalizedSourceEnergyPrefactor]
    calc
      ((Real.sqrt ((1 - alpha * ‖C.referenceRoot‖ ^ 2) ^ S.card))⁻¹ *
          Real.exp
            (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceResidual)) *
          (Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹ =
        Real.exp
            (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceResidual) *
          ((Real.sqrt
              ((1 - alpha * ‖C.referenceRoot‖ ^ 2) ^ S.card))⁻¹ *
            (Real.sqrt ((1 - 2 * beta) ^ S.card))⁻¹) := by ring
      _ ≤
        Real.exp
            (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceResidual) *
          Real.exp
            (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
              M d Nc C.referenceRoot alpha beta * (Z0.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [S] using hgaussian) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]
  exact hpoint.trans
    (mul_le_mul_of_nonneg_left
      (by simpa [S, beta] using hfactor)
      (mul_nonneg houter_nonneg (Real.exp_nonneg _)))

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
