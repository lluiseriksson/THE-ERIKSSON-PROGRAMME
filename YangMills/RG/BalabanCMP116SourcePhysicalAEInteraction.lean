/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePhysicalBondField
import YangMills.RG.BalabanCMP116Eq221AEInteractionAbsorption
import YangMills.RG.BalabanCMP116Eq214ConditionedOuterCarrier

/-!
# Source-specific almost-everywhere interaction bound

This module joins the literal physical potential, the literal bond field,
the bilateral complex `R2` estimate, and a certified conditioned Gaussian
root.  The result is exactly the almost-everywhere interaction hypothesis
consumed by the equation-(2.23) inner integration.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

namespace CMP116Eq214PhysicalContourDensity

/-- Restricting the outer Gaussian carrier changes `R1` and `R3`, but leaves
the inner `R2` interaction, bond field, and reference measure unchanged. -/
theorem ae_interactionExponent_le_withConditionedOuterCarrier
    {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
    {Psi Phi : Site → Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (SOuter SInner : Finset (Bond × Fin lieDim))
    (P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (gamma alpha residual : ℝ)
    (h :
      ∀ᵐ b ∂matrixGaussianPi C.referenceRoot,
        (C.toLocalFiniteGaussianData.interactionExponent
            sigma tau psi phi b).re +
          gamma / 2 * (∑ bond ∈ P, ‖C.bondField b bond‖ ^ 2) ≤
          alpha / 2 * (∑ i ∈ SInner, b i ^ 2) + residual) :
    ∀ᵐ b ∂matrixGaussianPi
        (C.withConditionedOuterCarrier SOuter).referenceRoot,
      ((C.withConditionedOuterCarrier SOuter).toLocalFiniteGaussianData.interactionExponent
          sigma tau
            (show RestrictedField
                (C.withConditionedOuterCarrier SOuter).spectatorSupport Psi
              from psi)
            (show RestrictedField
                (C.withConditionedOuterCarrier SOuter).fluctuationSupport Phi
              from phi)
            b).re +
        gamma / 2 *
          (∑ bond ∈ P,
            ‖(C.withConditionedOuterCarrier SOuter).bondField b bond‖ ^ 2) ≤
        alpha / 2 * (∑ i ∈ SInner, b i ^ 2) + residual := by
  simpa [withConditionedOuterCarrier, toLocalFiniteGaussianData, r2Matrix]
    using h

/-- The conditioned outer-carrier transport preserves any pointwise support
predicate on the Gaussian coordinate.  Instantiating `support` with the
literal cutoff-factor predicate avoids embedding the entire analytic-data
projection in this transport interface. -/
theorem ae_interactionExponent_le_withConditionedOuterCarrier_of_support
    {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
    {Psi Phi : Site → Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (SOuter SInner : Finset (Bond × Fin lieDim))
    (support : CMP116Eq214GaussianCoordinate Bond lieDim → Prop)
    (P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (gamma alpha residual : ℝ)
    (h :
      ∀ᵐ b ∂matrixGaussianPi C.referenceRoot,
        support b →
        (C.toLocalFiniteGaussianData.interactionExponent
            sigma tau psi phi b).re +
          gamma / 2 * (∑ bond ∈ P, ‖C.bondField b bond‖ ^ 2) ≤
          alpha / 2 * (∑ i ∈ SInner, b i ^ 2) + residual) :
    ∀ᵐ b ∂matrixGaussianPi
        (C.withConditionedOuterCarrier SOuter).referenceRoot,
      support b →
      ((C.withConditionedOuterCarrier SOuter).toLocalFiniteGaussianData.interactionExponent
          sigma tau
            (show RestrictedField
                (C.withConditionedOuterCarrier SOuter).spectatorSupport Psi
              from psi)
            (show RestrictedField
                (C.withConditionedOuterCarrier SOuter).fluctuationSupport Phi
              from phi)
            b).re +
        gamma / 2 *
          (∑ bond ∈ P,
            ‖(C.withConditionedOuterCarrier SOuter).bondField b bond‖ ^ 2) ≤
        alpha / 2 * (∑ i ∈ SInner, b i ^ 2) + residual := by
  simpa [withConditionedOuterCarrier, toLocalFiniteGaussianData, r2Matrix]
    using h

@[simp]
theorem cutoffFactor_withConditionedOuterCarrier
    {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
    {Psi Phi : Site → Type*}
    [Fintype Bond] [DecidableEq Bond] [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (S : Finset (Bond × Fin lieDim))
    (Y0 P : Finset Bond)
    (b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    (C.withConditionedOuterCarrier S).toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
        Y0 P b =
      C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.cutoffFactor
        Y0 P b := by
  change
    (-1 : ℂ) ^ P.card *
        cmp116SmallFieldCutoff Y0 C.threshold (C.bondField b) *
        cmp116LargeFieldCutoff P C.threshold (C.bondField b) =
      (-1 : ℂ) ^ P.card *
        cmp116SmallFieldCutoff Y0 C.threshold (C.bondField b) *
        cmp116LargeFieldCutoff P C.threshold (C.bondField b)
  rfl

/-- A direct potential estimate on the literal physical bond field is enough
to produce the almost-everywhere `alpha5` interaction bound.

This is the source-neutral absorption interface needed by centered Cauchy
contours: the potential estimate may already have combined the interpolation
center and contour displacement, so it must not be decomposed again into a
uniform kernel bound and a pointwise remainder bound. -/
theorem ae_interactionExponent_le_sourcePhysicalAlpha5_of_potential
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi
        (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
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
    {potentialRate r2Rate gamma alpha residual : ℝ}
    (hpotential :
      ∀ᵐ b ∂matrixGaussianPi C.referenceRoot,
        (C.potential sigma tau psi phi b).re ≤
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
        (Csource.potential sigma tau psi phi b).re ≤
          potentialRate / 2 * (∑ ba ∈ S, b ba ^ 2) + residual := by
    simpa [Csource, S] using hpotential
  have hR2' :
      (‖Csource.r2Matrix sigma tau psi phi‖ +
        ‖(Csource.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate := by
    simpa [Csource] using hR2
  have hresult :=
    cmp116Eq220_eq221_eq222_complexInteraction_le_localized_ae
      hroot (Csource.r2Matrix sigma tau psi phi)
      (fun b => Csource.potential sigma tau psi phi b)
      (fun b => ∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2)
      potentialRate r2Rate gamma alpha residual
      hpotential' hR2' hcutoff hgamma hbudget
  simpa [Csource, S] using hresult

/-- Equations (2.20)--(2.22) on the actual conditioned Gaussian: the
potential and large-field maps are literal, while the complex `R2` cost is
the volume-uniform bilateral Schur budget. -/
theorem ae_interactionExponent_le_sourcePhysicalAlpha5
    {nDelta nY d M N' Nc L lieDim : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)] [NeZero L] [NeZero lieDim]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (PhysicalBond d (M * N')) Site Psi Phi
        (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (D : Finset (Fin nY))
    (quadratic :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc →
        PhysicalEndomorphism d (M * N') Nc)
    (remainder :
      (Fin nDelta → ℂ) →
      RestrictedField C.spectatorSupport Psi →
      RestrictedField C.fluctuationSupport Phi →
      Fin nY → PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (amplitude residualWeight : Fin nY → ℝ)
    {kappa rowSum threshold potentialRate r2Rate gamma alpha : ℝ}
    (Z0 : Finset (FinBox d N'))
    (P : Finset (PhysicalBond d (M * N')))
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
    (hrowSum : 0 ≤ rowSum)
    (hrow : ∀ target : PhysicalBond d (M * N'),
      ∑ source : PhysicalBond d (M * N'),
        Real.exp (-(kappa *
          (physicalBondDist target source : ℝ))) ≤ rowSum)
    (hquadratic : ∀ b y, y ∈ D →
      PhysicalCovarianceExponentialKernelBound
        (quadratic sigma psi phi y
          (physicalBondProjection
            (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
            (cmp116SourcePhysicalCoordinateCochain b)))
        physicalBondDist (amplitude y) kappa)
    (hremainder : ∀ b y, y ∈ D →
      ‖tau y‖ *
          |remainder sigma psi phi y
            (physicalBondProjection
              (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
              (cmp116SourcePhysicalCoordinateCochain b))| ≤
        residualWeight y)
    (hpotentialRate :
      (∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum) ≤ potentialRate)
    (hR2 :
      (‖C.r2Matrix sigma tau psi phi‖ +
        ‖(C.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate)
    (hgamma : 0 ≤ gamma)
    (hbudget : potentialRate + r2Rate + gamma ≤ alpha) :
    let Csource :=
      (C.withSourcePhysicalComplexTauPotential
        Dict D quadratic remainder Z0).withSourcePhysicalBondField threshold
    ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
      (Csource.toLocalFiniteGaussianData.interactionExponent
          sigma tau psi phi b).re +
        gamma / 2 *
          (∑ bond ∈ P,
            ‖Csource.bondField b bond‖ ^ 2) ≤
        alpha / 2 *
          (∑ ba ∈ cmp116SourcePhysicalLocalizedCoordinates Dict Z0,
            b ba ^ 2) +
          ∑ y ∈ D, residualWeight y := by
  dsimp only
  let Cpotential :=
    C.withSourcePhysicalComplexTauPotential
      Dict D quadratic remainder Z0
  let Csource := Cpotential.withSourcePhysicalBondField threshold
  let S := cmp116SourcePhysicalLocalizedCoordinates Dict Z0
  let potentialRate' :=
    ∑ y ∈ D, ‖tau y‖ * amplitude y * rowSum
  have hpotential :
      ∀ᵐ b ∂matrixGaussianPi Csource.referenceRoot,
        (Csource.potential sigma tau psi phi b).re ≤
          potentialRate / 2 * (∑ ba ∈ S, b ba ^ 2) +
            ∑ y ∈ D, residualWeight y := by
    filter_upwards [] with b
    have hp :=
      C.re_withSourcePhysicalComplexTauPotential_potential_le_localized
        Dict D quadratic remainder amplitude residualWeight
        hrowSum hrow Z0 sigma tau psi phi b
        (hquadratic b) (hremainder b)
    have henergy : 0 ≤ ∑ ba ∈ S, b ba ^ 2 :=
      Finset.sum_nonneg fun ba hba => sq_nonneg _
    have hp' :
        (Csource.potential sigma tau psi phi b).re ≤
          potentialRate' / 2 * (∑ ba ∈ S, b ba ^ 2) +
            ∑ y ∈ D, residualWeight y := by
      simpa [Csource, Cpotential, S, potentialRate'] using hp
    exact hp'.trans (by
      gcongr)
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
  have hR2source :
      (‖Csource.r2Matrix sigma tau psi phi‖ +
        ‖(Csource.r2Matrix sigma tau psi phi).transpose‖) / 2 ≤ r2Rate := by
    simpa [Csource, Cpotential] using hR2
  have hresult :=
    cmp116Eq220_eq221_eq222_complexInteraction_le_localized_ae
      hroot (Csource.r2Matrix sigma tau psi phi)
      (fun b => Csource.potential sigma tau psi phi b)
      (fun b => ∑ bond ∈ P, ‖Csource.bondField b bond‖ ^ 2)
      potentialRate r2Rate gamma alpha
      (∑ y ∈ D, residualWeight y)
      hpotential hR2source hcutoff hgamma hbudget
  simpa [Csource, Cpotential, S] using hresult

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
