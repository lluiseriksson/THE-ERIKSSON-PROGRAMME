/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalContourCutoffSupport
import YangMills.RG.BalabanCMP116Eq226PhysicalContourResidualLedger

/-!
# Cutoff-support contour bound through the equation-(2.26) ledger

This is the source-faithful terminal counterpart of the unrestricted
physical-contour ledger.  The interaction estimate is required only where
the literal cutoff factor is nonzero; the cutoff itself handles the
complement.  All domain, gap, determinant, outer-energy, and rooted-residual
costs are then consumed exactly as in equation (2.26).
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

set_option maxHeartbeats 1200000 in
theorem norm_term_le_eq226SourceTermWeight_of_outerInteractionEnergy_cutoffSupport_residualLedger
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
  let boundaryMajorant :=
    (outerBound *
        Real.exp
          (residualSum - gamma / 2 * C.threshold ^ 2 * (P.card : ℝ))) *
      Real.exp (baseRate * (Z0.card : ℝ))
  let A :=
    C.toLocalFiniteGaussianData.toFiniteGaussianData.toAnalyticData
  have hterm :
      ‖A.term Y0 P psi phi‖ ≤
        ((boundaryMajorant *
          cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
            C2 kappa1 delta kappa domainMetric Finset.univ) *
          cmp116Eq226GapFactor kappa1 gapL M gapCard) := by
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
    · simpa [A, boundaryMajorant, baseRate] using
        (C.nestedCauchyBoundaryBound_of_outerInteractionEnergy_cutoffSupport_expCard
          Dict Y0 P Z0 psi phi alpha sourceRate 0 outerBound outerRate
          gamma residualSum r halpha hsmall hsourceRate houterRate hbeta
          houter_nonneg hgamma hthreshold_nonneg houter hinner
          (by simpa [residualSum] using hinteraction) hsource)
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
    simpa [A, boundaryMajorant] using hterm
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
