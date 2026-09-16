/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourOuterEnergy
import YangMills.RG.BalabanCMP116Eq226SigmaCauchy
import YangMills.RG.BalabanCMP116Eq220ResidualLedger

/-!
# Literal complex contour to the equation-(2.26) source ledger

This module consumes the two source Cauchy families after the complex contour
density has been bounded by the physically correct outer-energy route.  The
equation-(1.36) residual, equation-(2.22) `P` penalty, rank-localized
determinant, outer Gaussian moment, domain product, and normalized gap factor
are assembled into the literal equation-(2.26) source term weight.

No uniform pointwise bound on the `R1` outer factor and no post-hoc term
weight occur in the interface.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

/- Consume the literal source radii after the outer-energy boundary estimate.
The conclusion still exposes the residual and Gaussian costs separately so
that the rooted residual ledger can absorb them in the next theorem. -/
set_option maxHeartbeats 800000 in
theorem norm_term_le_eq226DomainGap_of_outerInteractionEnergy_cutoff
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N'))
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (alpha sourceRate sourceResidual outerBound outerRate gamma residual : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    (domainMetric : Fin nY → ℕ)
    (gapL gapCard : ℕ)
    (hDeltaRadius : C.deltaRadius =
      fun _ => cmp116Eq214SigmaCauchyRadius kappa1)
    (hnormalizedGap :
      ((((gapL * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
        (nDelta : ℝ))
    (hYRadius : C.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
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
    ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
        Y0 P psi phi‖ ≤
      (((outerBound *
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
              (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Finset.univ) *
        cmp116Eq226GapFactor kappa1 gapL M gapCard := by
  let A :=
    C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData
  let boundaryMajorant :=
    (outerBound *
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
            (Z0.card : ℝ))
  apply A.norm_term_le_eq226DomainGap_of_boundary
    Y0 P psi phi domainMetric gapL gapCard boundaryMajorant
  · simpa [A] using hDeltaRadius
  · exact hnormalizedGap
  · simpa [A] using hYRadius
  · exact hE0
  · exact hepsilon1
  · exact hC1
  · exact halpha4
  · exact hM
  · dsimp [boundaryMajorant]
    positivity
  · simpa [A, boundaryMajorant] using
      (C.nestedCauchyBoundaryBound_of_outerInteractionEnergy_cutoff_expCard
        Dict Y0 P Z0 psi phi alpha sourceRate sourceResidual outerBound
        outerRate gamma residual r halpha hsmall hsourceRate houterRate
        hbeta houter_nonneg hgamma hthreshold houter hinner hinteraction
        hsource)

/- Terminal literal-contour equation-(2.26) theorem.  The source residual is
the exact sum of equation-(1.36) domain weights; the source term itself has no
independent residual in the linear `R3` sector. -/
set_option maxHeartbeats 1000000 in
theorem norm_term_le_eq226SourceTermWeight_of_outerInteractionEnergy_residualLedger
    {nDelta nY d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N'))
    (psi : ∀ s, Psi s) (phi : ∀ s, Phi s)
    (alpha outerBound outerCost outerRate sourceRate gamma : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa gk : ℝ}
    (domainMetric : Fin nY → ℕ)
    (domainSupport : Fin nY → Finset (FinBox d N'))
    (gapL gapCard : ℕ)
    (rootBound Calpha : ℝ)
    (hDeltaRadius : C.deltaRadius =
      fun _ => cmp116Eq214SigmaCauchyRadius kappa1)
    (hnormalizedGap :
      ((((gapL * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
        (nDelta : ℝ))
    (hYRadius : C.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hgk : gk ≠ 0) (hthresholdEq : C.threshold = epsilon1 / gk)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * ‖C.referenceRoot‖ ^ 2 < 1)
    (hsourceRate : 0 ≤ sourceRate)
    (houterRate : 0 ≤ outerRate)
    (hbeta :
      2 * (outerRate +
        cmp116Eq225SourceCoefficient C.referenceRoot alpha *
          sourceRate) < 1)
    (houter_nonneg : 0 ≤ outerBound)
    (houter_card :
      outerBound ≤ Real.exp (outerCost * (Z0.card : ℝ)))
    (hgamma : 0 ≤ gamma) (hthreshold_nonneg : 0 ≤ C.threshold)
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
          ∑ Y : Fin nY,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainMetric Y : ℝ))
    (hsource : ∀ sigma tau,
      CMP116Eq214ShiftedPolydisc nDelta C.deltaRadius sigma →
      CMP116Eq214ShiftedPolydisc nY C.yRadius tau →
      ∀ x,
        (r sigma tau x) ⬝ᵥ (r sigma tau x) ≤
          sourceRate *
            (∑ i ∈ Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0,
              x i ^ 2) + 0)
    (hne : ∀ Y : Fin nY, (domainSupport Y).Nonempty)
    (hsub : ∀ Y : Fin nY, domainSupport Y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ Y ∈ (Finset.univ.filter fun Y : Fin nY =>
          i ∈ domainSupport Y),
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainMetric Y : ℝ) ≤ rootBound)
    (hvolumeBudget :
      rootBound +
          (PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
              M d Nc C.referenceRoot alpha
                (outerRate +
                  cmp116Eq225SourceCoefficient C.referenceRoot alpha *
                    sourceRate) +
            outerCost) ≤
        Calpha * alpha) :
    ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma gk gapL gapCard
        Calpha alpha Z0.card domainMetric Finset.univ P := by
  let residualSum :=
    ∑ Y : Fin nY,
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (domainMetric Y : ℝ)
  let baseRate :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
      M d Nc C.referenceRoot alpha
        (outerRate +
          cmp116Eq225SourceCoefficient C.referenceRoot alpha * sourceRate)
  have hterm :=
    C.norm_term_le_eq226DomainGap_of_outerInteractionEnergy_cutoff
      Dict Y0 P Z0 psi phi alpha sourceRate 0 outerBound outerRate gamma
      residualSum r domainMetric gapL gapCard hDeltaRadius hnormalizedGap
      hYRadius hE0 hepsilon1 hC1 halpha4 hM halpha hsmall hsourceRate
      houterRate hbeta houter_nonneg hgamma hthreshold_nonneg houter hinner
      (by simpa [residualSum] using hinteraction) hsource
  have hterm' :
      ‖C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData.term
          Y0 P psi phi‖ ≤
    ((outerBound *
          Real.exp
            (residualSum - gamma / 2 * C.threshold ^ 2 *
              (P.card : ℝ)) *
          Real.exp (baseRate * (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Finset.univ) *
        cmp116Eq226GapFactor kappa1 gapL M gapCard := by
    simpa [baseRate] using hterm
  refine hterm'.trans ?_
  apply
    cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_residualLedger_outerCard
    (D := (Finset.univ : Finset (Fin nY))) (P := P) (Z0 := Z0)
    domainSupport (fun Y => (domainMetric Y : ℝ)) domainMetric
    hE0.le hepsilon1.le hC1.le halpha4.le hgk hthresholdEq houter_card
  · intro Y _
    exact hne Y
  · intro Y _
    exact hsub Y
  · exact hroot
  · simpa [baseRate] using hvolumeBudget

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
