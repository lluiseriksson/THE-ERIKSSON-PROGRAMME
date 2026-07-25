/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexOuterLocalizedEnergy
import YangMills.RG.BalabanCMP116Eq214PhysicalContourOuterTraceIntegral
import YangMills.RG.BalabanCMP116Eq225SourceEnergy

/-!
# Equation (2.25) with the global `R1` trace bound

The inner Gaussian produces a localized source energy.  The literal complex
`R₁` and that localized energy are integrated together as one global outer
Gaussian.  This removes the pointwise `houter/outerRate` interface.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 3000000 in
/-- Fixed-contour equation-(2.25) estimate driven by symmetric trace tests for
the literal `R₁`, rather than a pointwise localized outer-energy estimate. -/
theorem norm_analyticIntegrand_le_of_outerTraceInteractionEnergy
    {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
    {Psi Phi : Site → Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    [Nonempty (Bond × Fin lieDim)]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (S : Finset (Bond × Fin lieDim))
    (alpha sourceRate sourceResidual determinantBound : ℝ)
    (r : CMP116Eq214GaussianCoordinate Bond lieDim →
      Bond × Fin lieDim → ℝ)
    (halpha : 0 ≤ alpha)
    (hrootSmall :
      alpha *
        (@norm (Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm C.referenceRoot) ^ 2 < 1)
    (hdet :
      ‖C.determinantDensity sigma tau
        (restrictGlobal C.spectatorSupport psi)
        (restrictGlobal C.fluctuationSupport phi)‖ ≤ determinantBound)
    (hdom : ∀ x,
      ∀ᵐ b ∂matrixGaussianPi C.referenceRoot,
        ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.innerIntegrand
            Y0 P sigma tau psi phi x b‖ ≤
          cmp116Eq223RealGaussian
            (-(alpha • cmp116Eq223CoordinateProjection S)) (r x) b)
    (hsource : ∀ x,
      (r x) ⬝ᵥ (r x) ≤
        sourceRate * (∑ i ∈ S, x i ^ 2) + sourceResidual)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart
        (C.r1Matrix sigma tau
            (restrictGlobal C.spectatorSupport psi)
            (restrictGlobal C.fluctuationSupport phi) +
          cmp116Eq214LocalizedOuterEnergyMatrix S
            (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceRate))).PosDef)
    (hsmall :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
        (C.r1Matrix sigma tau
            (restrictGlobal C.spectatorSupport psi)
            (restrictGlobal C.fluctuationSupport phi) +
          cmp116Eq214LocalizedOuterEnergyMatrix S
            (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceRate))).map Complex.ofRealHom‖ < 1)
    {L : ℝ} (hL : 0 ≤ L)
    (htrace : ∀ Q : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ,
      Q.transpose = Q →
      ‖Matrix.trace
        (C.r1Matrix sigma tau
          (restrictGlobal C.spectatorSupport psi)
          (restrictGlobal C.fluctuationSupport phi) * Q)‖ ≤ L * ‖Q‖) :
    ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.analyticIntegrand
        Y0 P sigma tau psi phi‖ ≤
      (determinantBound *
        cmp116Eq225LocalizedSourceEnergyPrefactor S
          C.referenceRoot alpha sourceResidual) *
        Real.exp
          (((L +
              2 *
                |cmp116Eq225SourceCoefficient C.referenceRoot alpha *
                  sourceRate| *
                (S.card : ℝ)) /
            (1 -
              ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
                (C.r1Matrix sigma tau
                    (restrictGlobal C.spectatorSupport psi)
                    (restrictGlobal C.fluctuationSupport phi) +
                  cmp116Eq214LocalizedOuterEnergyMatrix S
                    (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
                      sourceRate))).map Complex.ofRealHom‖)) / 2) := by
  let G := C.toLocalFiniteGaussianData.toFiniteGaussianData
  let psiR := restrictGlobal C.spectatorSupport psi
  let phiR := restrictGlobal C.fluctuationSupport phi
  let beta :=
    cmp116Eq225SourceCoefficient C.referenceRoot alpha * sourceRate
  let prefactor :=
    cmp116Eq225LocalizedSourceEnergyPrefactor S
      C.referenceRoot alpha sourceResidual
  let Acombined :=
    C.r1Matrix sigma tau psiR phiR +
      cmp116Eq214LocalizedOuterEnergyMatrix S beta
  have henergyEq : ∀ x : Bond × Fin lieDim → ℝ,
      (cmp116Eq214ComplexQuadratic Acombined x).re =
        (cmp116Eq214ComplexQuadratic
          (C.r1Matrix sigma tau psiR phiR) x).re +
          beta * ∑ i ∈ S, x i ^ 2 := by
    intro x
    rw [show Acombined =
      C.r1Matrix sigma tau psiR phiR +
        cmp116Eq214LocalizedOuterEnergyMatrix S beta by rfl]
    rw [cmp116Eq214ComplexQuadratic_add_localizedOuterEnergyMatrix,
      Complex.add_re, Complex.ofReal_re]
  have hdet0 : 0 ≤ determinantBound := (norm_nonneg _).trans hdet
  have hprefactor0 : 0 ≤ prefactor := by
    dsimp [prefactor, cmp116Eq225LocalizedSourceEnergyPrefactor,
      cmp116Eq225SourceCoefficient]
    positivity
  have hcombinedIntegrable :
      Integrable (fun x : Bond × Fin lieDim → ℝ =>
        Real.exp ((cmp116Eq214ComplexQuadratic Acombined x).re))
        (standardGaussianPi (Bond × Fin lieDim)) :=
    integrable_exp_re_complexQuadratic_standardGaussianPi
      Acombined (by simpa [Acombined, beta] using hpos)
  unfold CMP116Eq214AnalyticData.analyticIntegrand
  rw [G.toAnalyticData_mu0]
  unfold balabanCMP116Dmu0Flat
  calc
    ‖∫ x,
        G.outerWeight sigma tau psi phi x *
          ∫ b, G.toAnalyticData.innerIntegrand
              Y0 P sigma tau psi phi x b
            ∂G.toAnalyticData.conditionedMeasure sigma tau
        ∂standardGaussianPi (Bond × Fin lieDim)‖ ≤
      ∫ x,
        (determinantBound * prefactor) *
          Real.exp ((cmp116Eq214ComplexQuadratic Acombined x).re)
        ∂standardGaussianPi (Bond × Fin lieDim) := by
      apply norm_integral_le_of_norm_le
        (hcombinedIntegrable.const_mul (determinantBound * prefactor))
      filter_upwards [] with x
      rw [norm_mul]
      have hinner :=
        G.norm_innerIntegral_le_eq224Majorant_of_l2OpNormSmallness
          Y0 P sigma tau psi phi x S alpha (r x) halpha
          (by simpa [G] using hrootSmall)
          (by simpa [G] using hdom x)
      have hmajor :=
        cmp116Eq224_localized_gaussianMajorant_le_sourceEnergy_card
          S C.referenceRoot alpha (r x) x sourceRate sourceResidual
          halpha hrootSmall (hsource x)
      have houterEq := C.norm_outerWeight_eq sigma tau psiR phiR x
      have houterG :
          G.outerWeight sigma tau psi phi x =
            C.toLocalFiniteGaussianData.outerWeight
              sigma tau psiR phiR x := rfl
      rw [houterG]
      rw [houterEq]
      calc
        (‖C.determinantDensity sigma tau psiR phiR‖ *
            Real.exp
              ((cmp116Eq214ComplexQuadratic
                (C.r1Matrix sigma tau psiR phiR) x).re)) *
            ‖∫ b, G.toAnalyticData.innerIntegrand
                Y0 P sigma tau psi phi x b
              ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
          (determinantBound *
            Real.exp
              ((cmp116Eq214ComplexQuadratic
                (C.r1Matrix sigma tau psiR phiR) x).re)) *
            (prefactor * Real.exp (beta * ∑ i ∈ S, x i ^ 2)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hdet (Real.exp_nonneg _)
          · exact hinner.trans (by simpa [G, prefactor, beta] using hmajor)
          · exact norm_nonneg _
          · exact mul_nonneg hdet0 (Real.exp_nonneg _)
        _ = (determinantBound * prefactor) *
            Real.exp ((cmp116Eq214ComplexQuadratic Acombined x).re) := by
          rw [henergyEq x]
          rw [Real.exp_add]
          ring
    _ = (determinantBound * prefactor) *
        (∫ x,
          Real.exp ((cmp116Eq214ComplexQuadratic Acombined x).re)
          ∂standardGaussianPi (Bond × Fin lieDim)) := by
      rw [integral_const_mul]
    _ ≤ (determinantBound * prefactor) *
        Real.exp
          (((L + 2 * |beta| * (S.card : ℝ)) /
            (1 -
              ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart Acombined).map
                Complex.ofRealHom‖)) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hdet0 hprefactor0)
      have hgauss :=
        integral_exp_re_complexQuadratic_add_localizedEnergy_le_of_multiplier
          (C.r1Matrix sigma tau psiR phiR) S beta
          (by simpa [Acombined] using hpos)
          (by simpa [Acombined] using hsmall) hL
          (by simpa [psiR, phiR] using htrace)
      rw [integral_congr_ae
        (Filter.Eventually.of_forall fun x => by rw [henergyEq x])]
      simpa [Acombined, beta] using hgauss
    _ = _ := by rfl

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
