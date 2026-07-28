/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80CorrectedRectangularSourceJetBound
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainCoefficientRegularity
import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeSourceJetBound

/-!
# Second field derivative of one literal rectangular domain coefficient

The complete-domain FTC lane differentiates the equation-(80) potential
once in a rectangular propagator direction and then twice in the physical
field.  This module identifies that literal coefficient with the mixed
joint jet and constructs its two field derivatives without identifying it
with the separate square-typed Faà di Bruno activities.

The terminal estimate factors through the same reconstructed domain matrix
coefficient that already carries the source-metric decay.  Its component
budget reaches order three: this is the honest extra derivative consumed by
the occurrence of `fderiv V₀` in the propagator derivative.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CoarseField Q Nc →L[ℝ] FineField M Q Nc

section GenericRectangularDirectionalJet

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal propagator-directional derivative is exactly the first
joint propagator jet.  This is valid for genuinely rectangular propagators
`F →L E`; no identification of fine and coarse fields is used. -/
theorem
    cmp102Eq80PropagatorDirectionalDerivative_eq_partialPropagatorJet
    (D D₃ : E → F) (V₀ : E → ℝ)
    (H K : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    cmp102Eq80PropagatorDirectionalDerivative D D₃ H K Δπ J A
        (fderiv ℝ V₀ (A - H (D A))) =
      cmp102PartialPropagatorJet
        (fun p : (F →L[ℝ] E) × E =>
          cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
        1 H (fun _ => K) A := by
  let Φ : (F →L[ℝ] E) × E → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  rw [← iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
    Φ hΦ 1 H (fun _ => K) A]
  rw [iteratedFDeriv_one_apply]
  have hline :=
    hasDerivAt_cmp102Eq80GlobalPotential_affinePropagator
      D D₃ V₀ H K Δπ J A 0
      (fderiv ℝ V₀ (A - H (D A)))
      (by
        simpa using
          (hV₀.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have hpath : HasDerivAt (fun u : ℝ => H + u • K) K 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) H).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const K) using 1 <;>
      simp
  have hslice : ContDiff ℝ ⊤ (fun L : F →L[ℝ] E => Φ (L, A)) :=
    hΦ.comp (contDiff_id.prodMk contDiff_const)
  have hlineRaw :=
    (((hslice.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
      0 hpath).hasDerivAt)
  have hline' : HasDerivAt
      (fun u : ℝ => Φ (H + u • K, A))
      (fderiv ℝ (fun L : F →L[ℝ] E => Φ (L, A)) H K) 0 := by
    simpa [Function.comp_def] using hlineRaw
  simpa [Φ] using hline.unique hline'

end GenericRectangularDirectionalJet

/-- The literal complete-domain coefficient, with the physical first
derivative of `V₀` inserted, is exactly the first joint propagator jet.
This is the source-faithful bridge from the reconstructed `tsum`
coefficient to the rectangular jet lane. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_partialPropagatorJet
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (H : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ H Δπ J A
        (fderiv ℝ V₀ (A - H (D A))) Y =
      cmp102PartialPropagatorJet
        (fun p : RectangularFieldMap M Q Nc × FineField M Q Nc =>
          cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
        1 H
        (fun _ =>
          cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y))
        A := by
  rw [
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_derivative_matrixCoefficient
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ H Δπ J A (fderiv ℝ V₀ (A - H (D A))) Y]
  exact
    cmp102Eq80PropagatorDirectionalDerivative_eq_partialPropagatorJet
      D D₃ V₀ H
      (cmp99PhysicalRectangularOfComplexMatrix
        (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice Y))
      Δπ J A hD hD₃ hV₀

/-- The first physical-field derivative of one complete rectangular
domain coefficient, written as the corresponding mixed joint jet. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainCoefficientFirstFieldDerivative
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (H : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q))) :
    FineField M Q Nc →L[ℝ] ℝ :=
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  cmp102PartialPropagatorJetFieldDerivative
    (fun p : RectangularFieldMap M Q Nc × FineField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
    1 H (fun _ => Kdomain) A

/-- The second physical-field derivative of one complete rectangular
domain coefficient. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (H : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q))) :
    FineField M Q Nc →L[ℝ] FineField M Q Nc →L[ℝ] ℝ :=
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  cmp102PartialPropagatorJetSecondFieldDerivative
    (fun p : RectangularFieldMap M Q Nc × FineField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
    1 H (fun _ => Kdomain) A

/-- The displayed second field derivative differentiates the displayed
first field derivative. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainCoefficientFirstFieldDerivative_hasFDerivAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (H : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    HasFDerivAt
      (fun X =>
        cmp102Eq80PhysicalFineHeadTailDomainCoefficientFirstFieldDerivative
          anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice
          D D₃ V₀ H Δπ J X Y)
      (cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ H Δπ J A Y) A := by
  let Φ :
      RectangularFieldMap M Q Nc × FineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  simpa [
    cmp102Eq80PhysicalFineHeadTailDomainCoefficientFirstFieldDerivative,
    cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative,
    Φ] using
    cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
      Φ hΦ 1 H
      (fun _ =>
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y)) A

/-- The Fréchet derivative of the literal complete-domain coefficient is
the displayed first field derivative.  All reconstruction and summability
hypotheses are consumed here, so downstream radial FTC arguments need not
identify the coefficient with a synthetic activity. -/
theorem
    fderiv_cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_firstFieldDerivative
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (H : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    fderiv ℝ
        (fun X =>
          cmp102Eq80PhysicalFineHeadTailDomainCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ H Δπ J X
            (fderiv ℝ V₀ (X - H (D X))) Y)
        A =
      cmp102Eq80PhysicalFineHeadTailDomainCoefficientFirstFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ H Δπ J A Y := by
  let Φ :
      RectangularFieldMap M Q Nc × FineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  have hfun :
      (fun X =>
        cmp102Eq80PhysicalFineHeadTailDomainCoefficient
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ H Δπ J X
          (fderiv ℝ V₀ (X - H (D X))) Y) =
        cmp102PartialPropagatorJet Φ 1 H (fun _ => Kdomain) := by
    funext X
    simpa [Φ, Kdomain] using
      cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_partialPropagatorJet
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmall layerWord choice
        D D₃ V₀ H Δπ J X Y hD hD₃ hV₀
  rw [hfun,
    fderiv_cmp102PartialPropagatorJet_eq_fieldDerivative
      Φ hΦ 1 H (fun _ => Kdomain) A]
  rfl

/-- The second field derivative is bounded by the order-three
source-generated joint majorant times the literal reconstructed domain
matrix norm.  No bound for the complete Hessian or for the final domain
activity is assumed. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative_le_sourceJets
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (H : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet : ℝ)
    (hC : ∀ i, i ≤ 3 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D (H, A))‖ ≤ C)
    (hRjet : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i
          (fun q :
              RectangularFieldMap M Q Nc × FineField M Q Nc => q.2)
          (H, A)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i (H, A) ≤ Rjet ^ i) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ H Δπ J A Y‖ ≤
      cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 3 (H, A) C Rjet *
        ‖cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y)‖ := by
  let Φ :
      RectangularFieldMap M Q Nc × FineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  have hraw :=
    norm_cmp102PartialPropagatorJetSecondFieldDerivative_le
      Φ 1 H (fun _ => Kdomain) A
  have hjoint :
      ‖iteratedFDeriv ℝ 3 Φ (H, A)‖ ≤
        cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 3 (H, A) C Rjet := by
    simpa [Φ] using
      norm_iteratedFDeriv_cmp102Eq80JointPotential_le_sourceJetMajorant
        D D₃ V₀ Δπ J hD hD₃ hV₀ 3 (H, A) C Rjet hC hRjet
  calc
    ‖cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ H Δπ J A Y‖ ≤
      ‖iteratedFDeriv ℝ 3 Φ (H, A)‖ * ‖Kdomain‖ := by
        simpa [
          cmp102Eq80PhysicalFineHeadTailDomainCoefficientSecondFieldDerivative,
          Φ, Kdomain] using hraw
    _ ≤ cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 3 (H, A) C Rjet * ‖Kdomain‖ :=
      mul_le_mul_of_nonneg_right hjoint (norm_nonneg Kdomain)
    _ = _ := by rfl

end

end YangMills.RG
