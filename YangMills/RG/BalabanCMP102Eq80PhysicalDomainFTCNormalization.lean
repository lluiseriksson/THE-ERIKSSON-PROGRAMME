/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCSecondFieldDerivative
import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainFirstOrder

/-!
# Source normalization of the literal rectangular domain FTC contribution

The reconstructed complete-domain contribution is a first propagator jet
integrated along the affine physical minimizer segment.  This module proves
its order-zero and order-one normalization directly from the literal
equation-(80) source identities.

The propagator is genuinely rectangular.  No identification of the fine and
coarse physical fields is made, no normalization of the final activity is
supplied as a premise, and this contribution is not identified with the
separate residual `V''_k`.
-/

open MeasureTheory
open scoped Interval RealInnerProductSpace

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

section GenericRectangularNormalization

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a smooth joint functional vanishes on the complete zero-field
slice, then every partial propagator jet vanishes there. -/
theorem cmp102PartialPropagatorJet_zero_of_zero_field_slice
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (hzero : ∀ h : H, F (h, 0) = 0)
    (n : ℕ) (h : H) (v : Fin n → H) :
    cmp102PartialPropagatorJet F n h v 0 = 0 := by
  rw [← iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
    F hF n h v 0]
  have hslice :
      (fun y : H => F (y, (0 : E))) = (fun _ : H => 0) := by
    funext y
    exact hzero y
  rw [hslice]
  simp

/-- The affine FTC integral of a zero-field propagator jet vanishes. -/
theorem cmp102AffinePropagatorJetFTC_zero_of_zero_field_slice
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (hzero : ∀ h : H, F (h, 0) = 0)
    (n : ℕ) (P T : H) (v : Fin n → H) :
    cmp102AffinePropagatorJetFTC F n P T v 0 = 0 := by
  unfold cmp102AffinePropagatorJetFTC
  calc
    (∫ t in (0 : ℝ)..1,
        cmp102PartialPropagatorJet F n (P + t • T) v 0) =
        ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          exact
            cmp102PartialPropagatorJet_zero_of_zero_field_slice
              F hF hzero n (P + t • T) v
    _ = 0 := by simp

/-- If the vertical derivative of the joint functional vanishes on the
zero-field slice, then the integrated first field derivative of every
affine propagator jet vanishes there. -/
theorem
    cmp102AffinePropagatorJetFTCFirstFieldDerivative_zero_of_vertical_slice
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (hpartial : ∀ h : H, ∀ a : E,
      fderiv ℝ F (h, 0) (0, a) = 0)
    (n : ℕ) (P T : H) (v : Fin n → H) :
    cmp102AffinePropagatorJetFTCFirstFieldDerivative
        F n P T v 0 = 0 := by
  unfold cmp102AffinePropagatorJetFTCFirstFieldDerivative
  calc
    (∫ t in (0 : ℝ)..1,
        cmp102PartialPropagatorJetFieldDerivative
          F n (P + t • T) v 0) =
        ∫ _t in (0 : ℝ)..1, (0 : E →L[ℝ] ℝ) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          have hactual :=
            cmp102PartialPropagatorJet_hasFDerivAt
              F hF n (P + t • T) v (0 : E)
          have hzero :=
            hasFDerivAt_cmp102PartialPropagatorJet_zero
              F hF hpartial n (P + t • T) v
          exact hactual.unique hzero
    _ = 0 := by simp

end GenericRectangularNormalization

section RectangularEq80Normalization

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The physical-field derivative of the rectangular joint equation-(80)
functional vanishes on the whole zero-field propagator slice. -/
theorem fderiv_cmp102Eq80JointPotential_rectangular_vertical_zero
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Δπ : E →L[ℝ] E) (J : E)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃ (0 : E →L[ℝ] F) 0)
    (hV₀' : HasFDerivAt V₀ (0 : E →L[ℝ] ℝ) 0)
    (H : F →L[ℝ] E) (a : E) :
    fderiv ℝ
      (fun p : (F →L[ℝ] E) × E =>
        cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
      (H, 0) (0, a) = 0 := by
  let Φ : (F →L[ℝ] E) × E → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  have hpath : HasFDerivAt (fun x : E => (H, x))
      ((0 : E →L[ℝ] (F →L[ℝ] E)).prod
        (1 : E →L[ℝ] E)) 0 :=
    (hasFDerivAt_const (x := (0 : E)) H).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E)))
  have hcomp :=
    (hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
      (0 : E) hpath
  have hD' : HasFDerivAt D (fderiv ℝ D 0) 0 :=
    (hD.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hslice :=
    cmp102Eq80GlobalPotential_hasFDerivAt_zero
      D D₃ V₀ H Δπ J (fderiv ℝ D 0)
      hD0 hD₃0 hD' hD₃' hV₀'
  have heq := hcomp.unique hslice
  have heval := congrArg (fun T => T a) heq
  simpa [Φ] using heval

end RectangularEq80Normalization

/-- The literal reconstructed complete-domain FTC contribution vanishes at
the zero fine field. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_zero_field
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
    (P T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J 0 Y = 0 := by
  rw [
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_affinePropagatorJetFTC
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ V₀ P T Δπ J 0 Y hD hD₃ hV₀]
  apply cmp102AffinePropagatorJetFTC_zero_of_zero_field_slice
  · exact
      contDiff_cmp102Eq80JointPotential_rectangular
        D D₃ V₀ Δπ J hD hD₃ hV₀
  · intro H
    exact cmp102Eq80GlobalPotential_zero
      D D₃ V₀ H Δπ J hD0 hD₃0 hV₀0

/-- The explicit first derivative of the literal complete-domain FTC
contribution vanishes at the zero fine field. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative_zero_field
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
    (P T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0) :
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J 0 Y = 0 := by
  let Φ :
      RectangularFieldMap M Q Nc × FineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  have hpartial :
      ∀ H : RectangularFieldMap M Q Nc,
        ∀ a : FineField M Q Nc,
          fderiv ℝ Φ (H, 0) (0, a) = 0 := by
    intro H a
    exact
      fderiv_cmp102Eq80JointPotential_rectangular_vertical_zero
        D D₃ V₀ Δπ J hD hD₃ hV₀
        hD0 hD₃0 hD₃' hV₀' H a
  simpa [
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative,
    Φ] using
    cmp102AffinePropagatorJetFTCFirstFieldDerivative_zero_of_vertical_slice
      Φ hΦ hpartial 1 P T
      (fun _ =>
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice Y))

/-- The Fréchet derivative of the literal complete-domain FTC contribution
at the zero fine field is the zero continuous linear map.  This is the
normalization consumed by the radial Taylor operator. -/
theorem
    fderiv_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_zero_field
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
    (P T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : FineField M Q Nc →L[ℝ] CoarseField Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : FineField M Q Nc →L[ℝ] ℝ) 0) :
    fderiv ℝ
      (fun X =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J X Y)
      0 = 0 := by
  calc
    fderiv ℝ
        (fun X =>
          cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
            anchor K hc hmass hK baseCoarseCovariance
            sigma layerWord choice D D₃ V₀ P T Δπ J X Y)
        0 =
      cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J 0 Y :=
          (cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_hasFDerivAt
            anchor K hc hmass hK baseCoarseCovariance
            hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
            sigma hRweak hcap hsmall layerWord choice
            D D₃ V₀ P T Δπ J 0 Y hD hD₃ hV₀).fderiv
    _ = 0 :=
      cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative_zero_field
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J Y
        hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀'

end

end YangMills.RG
