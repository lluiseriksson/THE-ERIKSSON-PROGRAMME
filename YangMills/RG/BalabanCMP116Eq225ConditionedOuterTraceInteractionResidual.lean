/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq225OuterTraceInteractionResidual

/-!
# Residual-preserving trace integration with two localization carriers

Equation (2.23) uses `SInner` for the conditioned `B` Gaussian and
`SOuter` for the outer `X` Gaussian.  The two carriers need not coincide.
This module performs the two integrations with those roles kept distinct.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

/-- The determinant is localized on the conditioned `B` carrier `SInner`,
whereas the source energy is measured on the outer `X` carrier `SOuter`.
Equation (2.23) requires these two carriers to remain distinct. -/
theorem cmp116Eq224_localized_gaussianMajorant_le_conditionedSourceEnergy_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (SInner SOuter : Finset ι) (R : Matrix ι ι ℝ) (alpha : ℝ)
    (r x : ι → ℝ) (sourceRate sourceResidual : ℝ)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha *
      (@norm (Matrix ι ι ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2 < 1)
    (hsource : r ⬝ᵥ r ≤
      sourceRate * (∑ i ∈ SOuter, x i ^ 2) + sourceResidual) :
    cmp116Eq224GaussianMajorant R
        (-(alpha • cmp116Eq223CoordinateProjection SInner))
        (fun i => (r i : ℂ)) ≤
      cmp116Eq225LocalizedSourceEnergyPrefactor SInner R alpha sourceResidual *
        Real.exp
          ((cmp116Eq225SourceCoefficient R alpha * sourceRate) *
            ∑ i ∈ SOuter, x i ^ 2) := by
  refine (cmp116Eq224_localized_gaussianMajorant_le_card
    SInner R alpha r halpha hsmall).trans ?_
  have hdenom : 0 < 2 * (1 - alpha *
      (@norm (Matrix ι ι ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2) := by
    have hd : 0 < 1 - alpha *
        (@norm (Matrix ι ι ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2 :=
      sub_pos.mpr hsmall
    nlinarith
  have hcoeff : 0 ≤ cmp116Eq225SourceCoefficient R alpha := by
    unfold cmp116Eq225SourceCoefficient
    exact div_nonneg
      (sq_nonneg
        (@norm (Matrix ι ι ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm R))
      hdenom.le
  unfold cmp116Eq225LocalizedSourceEnergyPrefactor
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold cmp116Eq225SourceCoefficient
    calc
      ((@norm (Matrix ι ι ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2 * (r ⬝ᵥ r)) /
          (2 * (1 - alpha *
            (@norm (Matrix ι ι ℝ)
              Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2)) =
        ((@norm (Matrix ι ι ℝ)
            Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2 /
          (2 * (1 - alpha *
            (@norm (Matrix ι ι ℝ)
              Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2))) *
          (r ⬝ᵥ r) := by ring
      _ ≤
        ((@norm (Matrix ι ι ℝ)
            Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2 /
          (2 * (1 - alpha *
            (@norm (Matrix ι ι ℝ)
              Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2))) *
          (sourceRate * ∑ i ∈ SOuter, x i ^ 2 + sourceResidual) := by
            exact mul_le_mul_of_nonneg_left hsource hcoeff
      _ =
        ((@norm (Matrix ι ι ℝ)
            Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2 /
          (2 * (1 - alpha *
            (@norm (Matrix ι ι ℝ)
              Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2))) *
          sourceResidual +
        (((@norm (Matrix ι ι ℝ)
            Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2 /
          (2 * (1 - alpha *
            (@norm (Matrix ι ι ℝ)
              Matrix.instL2OpNormedAddCommGroup.toNorm R) ^ 2))) *
          sourceRate) *
          ∑ i ∈ SOuter, x i ^ 2 := by ring
  · positivity

set_option maxHeartbeats 6000000 in
/-- Fixed-contour equation-(2.25) estimate with distinct inner and outer
carriers. -/
theorem norm_analyticIntegrand_le_of_conditionedOuterTraceInteractionEnergy_cutoff
    {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
    {Psi Phi : Site → Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    [Nonempty (Bond × Fin lieDim)]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (SInner SOuter : Finset (Bond × Fin lieDim))
    (alpha sourceRate determinantBound gamma residual : ℝ)
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
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ C.threshold)
    (hinner : ∀ x b,
      ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.innerWeight
          sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r x i * b i))
    (hinteraction : ∀ b,
      (C.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        (gamma / 2) *
          (∑ e ∈ P,
            ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
              b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          Matrix.mulVec
            (-(alpha • cmp116Eq223CoordinateProjection SInner)) b) / 2) +
          residual)
    (hsource : ∀ x,
      (r x) ⬝ᵥ (r x) ≤
        sourceRate * (∑ i ∈ SOuter, x i ^ 2) + 0)
    (hpos :
      (1 - cmp116Eq214ComplexQuadraticSymmetricRealPart
        (C.r1Matrix sigma tau
            (restrictGlobal C.spectatorSupport psi)
            (restrictGlobal C.fluctuationSupport phi) +
          cmp116Eq214LocalizedOuterEnergyMatrix SOuter
            (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceRate))).PosDef)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcombinedRadius :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
        (C.r1Matrix sigma tau
            (restrictGlobal C.spectatorSupport psi)
            (restrictGlobal C.fluctuationSupport phi) +
          cmp116Eq214LocalizedOuterEnergyMatrix SOuter
            (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
              sourceRate))).map Complex.ofRealHom‖ ≤ q)
    {L : ℝ} (hL : 0 ≤ L)
    (htrace : ∀ Q : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ,
      Q.transpose = Q →
      ‖Matrix.trace
        (C.r1Matrix sigma tau
          (restrictGlobal C.spectatorSupport psi)
          (restrictGlobal C.fluctuationSupport phi) * Q)‖ ≤ L * ‖Q‖) :
    ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.analyticIntegrand
        Y0 P sigma tau psi phi‖ ≤
      Real.exp
          (residual - gamma / 2 * C.threshold ^ 2 * (P.card : ℝ)) *
        ((determinantBound *
          cmp116Eq225LocalizedSourceEnergyPrefactor SInner
            C.referenceRoot alpha 0) *
          Real.exp
            (((L +
                2 *
                  |cmp116Eq225SourceCoefficient C.referenceRoot alpha *
                    sourceRate| *
                  (SOuter.card : ℝ)) /
              (1 - q)) / 2)) := by
  let G := C.toLocalFiniteGaussianData.toFiniteGaussianData
  let psiR := restrictGlobal C.spectatorSupport psi
  let phiR := restrictGlobal C.fluctuationSupport phi
  let beta :=
    cmp116Eq225SourceCoefficient C.referenceRoot alpha * sourceRate
  let scale :=
    Real.exp
      (residual - gamma / 2 * C.threshold ^ 2 * (P.card : ℝ))
  let prefactor :=
    cmp116Eq225LocalizedSourceEnergyPrefactor SInner
      C.referenceRoot alpha 0
  let Acombined :=
    C.r1Matrix sigma tau psiR phiR +
      cmp116Eq214LocalizedOuterEnergyMatrix SOuter beta
  have henergyEq : ∀ x : Bond × Fin lieDim → ℝ,
      (cmp116Eq214ComplexQuadratic Acombined x).re =
        (cmp116Eq214ComplexQuadratic
          (C.r1Matrix sigma tau psiR phiR) x).re +
          beta * ∑ i ∈ SOuter, x i ^ 2 := by
    intro x
    rw [show Acombined =
      C.r1Matrix sigma tau psiR phiR +
        cmp116Eq214LocalizedOuterEnergyMatrix SOuter beta by rfl]
    rw [cmp116Eq214ComplexQuadratic_add_localizedOuterEnergyMatrix,
      Complex.add_re, Complex.ofReal_re]
  have hdet0 : 0 ≤ determinantBound := (norm_nonneg _).trans hdet
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hprefactor0 : 0 ≤ prefactor := by
    dsimp [prefactor, cmp116Eq225LocalizedSourceEnergyPrefactor,
      cmp116Eq225SourceCoefficient]
    positivity
  have hinnerPos :
      (1 + (C.referenceRoot).transpose *
        (-(alpha • cmp116Eq223CoordinateProjection SInner)) *
          C.referenceRoot).PosDef := by
    simpa [sub_eq_add_neg, Matrix.mul_neg] using
      (posDef_one_sub_localized_covariance_of_l2_opNorm_small
        SInner C.referenceRoot alpha halpha hrootSmall)
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
        (scale * (determinantBound * prefactor)) *
          Real.exp ((cmp116Eq214ComplexQuadratic Acombined x).re)
        ∂standardGaussianPi (Bond × Fin lieDim) := by
      apply norm_integral_le_of_norm_le
        (hcombinedIntegrable.const_mul
          (scale * (determinantBound * prefactor)))
      filter_upwards [] with x
      rw [norm_mul]
      have hinnerIntegral :=
        G.norm_innerIntegral_le_exp_residual_sub_cardPenalty_mul_eq224Majorant
          Y0 P sigma tau psi phi x
          (-(alpha • cmp116Eq223CoordinateProjection SInner)) (r x)
          gamma residual
          (by simpa [G] using hgamma)
          (by simpa [G] using hthreshold)
          (by simpa [G] using hinnerPos)
          (by simpa [G] using hinner x)
          (by simpa [G] using hinteraction)
      have hmajor :=
        cmp116Eq224_localized_gaussianMajorant_le_conditionedSourceEnergy_card
          SInner SOuter C.referenceRoot alpha (r x) x sourceRate 0
          halpha hrootSmall (hsource x)
      have houterEq := C.norm_outerWeight_eq sigma tau psiR phiR x
      have houterG :
          G.outerWeight sigma tau psi phi x =
            C.toLocalFiniteGaussianData.outerWeight
              sigma tau psiR phiR x := rfl
      rw [houterG, houterEq]
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
            (scale *
              (prefactor *
                Real.exp (beta * ∑ i ∈ SOuter, x i ^ 2))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hdet (Real.exp_nonneg _)
          · exact hinnerIntegral.trans
              (mul_le_mul_of_nonneg_left
                (by simpa [G, prefactor, beta] using hmajor) hscale0)
          · exact norm_nonneg _
          · exact mul_nonneg hdet0 (Real.exp_nonneg _)
        _ = (scale * (determinantBound * prefactor)) *
            Real.exp ((cmp116Eq214ComplexQuadratic Acombined x).re) := by
          rw [henergyEq x, Real.exp_add]
          ring
    _ = (scale * (determinantBound * prefactor)) *
        (∫ x,
          Real.exp ((cmp116Eq214ComplexQuadratic Acombined x).re)
          ∂standardGaussianPi (Bond × Fin lieDim)) := by
      rw [integral_const_mul]
    _ ≤ (scale * (determinantBound * prefactor)) *
        Real.exp
          (((L + 2 * |beta| * (SOuter.card : ℝ)) /
            (1 - q)) / 2) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hscale0 (mul_nonneg hdet0 hprefactor0))
      have hgauss :=
        integral_exp_re_complexQuadratic_add_localizedEnergy_le_of_radius
          (C.r1Matrix sigma tau psiR phiR) SOuter beta
          (by simpa [Acombined] using hpos)
          hq0 hq1 hL
          (by simpa [Acombined, beta, psiR, phiR] using hcombinedRadius)
          (by simpa [psiR, phiR] using htrace)
      rw [integral_congr_ae
        (Filter.Eventually.of_forall fun x => by rw [henergyEq x])]
      simpa [Acombined, beta] using hgauss
    _ = _ := by
      dsimp [scale, prefactor, beta]
      ring

/-- Shifted-polydisc boundary with separate inner and outer carriers. -/
theorem
    nestedCauchyBoundaryBound_of_conditionedOuterTraceInteractionEnergy_cutoff_onPolydiscs
    {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
    {Psi Phi : Site → Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    [Nonempty (Bond × Fin lieDim)]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (Y0 P : Finset Bond)
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (SInner SOuter : Finset (Bond × Fin lieDim))
    (alpha sourceRate determinantBound gamma residual : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate Bond lieDim →
        Bond × Fin lieDim → ℝ)
    (halpha : 0 ≤ alpha)
    (hrootSmall :
      alpha *
        (@norm (Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℝ)
          Matrix.instL2OpNormedAddCommGroup.toNorm C.referenceRoot) ^ 2 < 1)
    {q L : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hL : 0 ≤ L)
    (hdet : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ‖C.determinantDensity sigma tau
        (restrictGlobal C.spectatorSupport psi)
        (restrictGlobal C.fluctuationSupport phi)‖ ≤ determinantBound)
    (hgamma : 0 ≤ gamma) (hthreshold : 0 ≤ C.threshold)
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
      (C.toLocalFiniteGaussianData.toFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        (gamma / 2) *
          (∑ e ∈ P,
            ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.bondField
              b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          Matrix.mulVec
            (-(alpha • cmp116Eq223CoordinateProjection SInner)) b) / 2) +
          residual)
    (hsource : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ x,
      (r sigma tau x) ⬝ᵥ (r sigma tau x) ≤
        sourceRate * (∑ i ∈ SOuter, x i ^ 2) + 0)
    (hbilateral : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      (‖C.r1Matrix sigma tau
          (restrictGlobal C.spectatorSupport psi)
          (restrictGlobal C.fluctuationSupport phi)‖ +
        ‖(C.r1Matrix sigma tau
          (restrictGlobal C.spectatorSupport psi)
          (restrictGlobal C.fluctuationSupport phi)).transpose‖) / 2 +
        2 *
          |cmp116Eq225SourceCoefficient C.referenceRoot alpha *
            sourceRate| ≤ q)
    (htrace : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ Q : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ,
      Q.transpose = Q →
      ‖Matrix.trace
        (C.r1Matrix sigma tau
          (restrictGlobal C.spectatorSupport psi)
          (restrictGlobal C.fluctuationSupport phi) * Q)‖ ≤ L * ‖Q‖) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      C.deltaRadius C.yRadius
      (fun sigma tau =>
        C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.analyticIntegrand
          Y0 P sigma tau psi phi)
      (Real.exp
          (residual - gamma / 2 * C.threshold ^ 2 * (P.card : ℝ)) *
        ((determinantBound *
          cmp116Eq225LocalizedSourceEnergyPrefactor SInner
            C.referenceRoot alpha 0) *
          Real.exp
            (((L +
                2 *
                  |cmp116Eq225SourceCoefficient C.referenceRoot alpha *
                    sourceRate| *
                  (SOuter.card : ℝ)) /
              (1 - q)) / 2))) := by
  apply cmp116Eq214NestedCauchyBoundaryBound_of_shiftedPolydiscs
  intro sigma tau hsigma htau
  apply
    C.norm_analyticIntegrand_le_of_conditionedOuterTraceInteractionEnergy_cutoff
      Y0 P sigma tau psi phi SInner SOuter alpha sourceRate
      determinantBound gamma residual (r sigma tau) halpha hrootSmall
      (hdet sigma tau hsigma htau) hgamma hthreshold
      (hinner sigma tau hsigma htau)
      (hinteraction sigma tau hsigma htau)
      (hsource sigma tau hsigma htau)
  · apply
      posDef_one_sub_symmetricRealPart_add_localizedEnergy_of_bilateral_small
    exact (hbilateral sigma tau hsigma htau).trans_lt hq1
  · exact hq0
  · exact hq1
  · exact
      (norm_complexified_neg_symmetricRealPart_add_localizedEnergy_le
        (C.r1Matrix sigma tau
          (restrictGlobal C.spectatorSupport psi)
          (restrictGlobal C.fluctuationSupport phi))
        SOuter
        (cmp116Eq225SourceCoefficient C.referenceRoot alpha *
          sourceRate)).trans
        (hbilateral sigma tau hsigma htau)
  · exact hL
  · exact htrace sigma tau hsigma htau

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
