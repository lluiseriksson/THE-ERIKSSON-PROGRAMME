/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainCoefficientSecondFieldDerivative
import YangMills.RG.BalabanCMP102Eq80ParametricIntervalFirstOrder
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCContribution

/-!
# Two physical-field derivatives through one literal domain FTC integral

The complete physical-domain contribution is an integral over the affine
propagator segment.  This module differentiates that literal integral
twice in the fine physical field.  Both derivatives are generated from the
rectangular joint jets proved for the reconstructed domain coefficient.

No derivative of the final activity is supplied as a premise.  Compactness
of the field ball times `[0,1]` generates the domination required to
differentiate under the interval integral.
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

section GenericAffineJetFTC

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Integral of one partial propagator jet along an affine propagator
segment. -/
noncomputable def cmp102AffinePropagatorJetFTC
    (F : H × E → ℝ) (n : ℕ) (P T : H)
    (v : Fin n → H) (x : E) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    cmp102PartialPropagatorJet F n (P + t • T) v x

/-- First physical-field derivative of the affine jet integral. -/
noncomputable def cmp102AffinePropagatorJetFTCFirstFieldDerivative
    (F : H × E → ℝ) (n : ℕ) (P T : H)
    (v : Fin n → H) (x : E) : E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1,
    cmp102PartialPropagatorJetFieldDerivative
      F n (P + t • T) v x

/-- Second physical-field derivative of the affine jet integral. -/
noncomputable def cmp102AffinePropagatorJetFTCSecondFieldDerivative
    (F : H × E → ℝ) (n : ℕ) (P T : H)
    (v : Fin n → H) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1,
    cmp102PartialPropagatorJetSecondFieldDerivative
      F n (P + t • T) v x

/-- The first derivative commutes with the literal affine FTC integral.
The dominating bound is generated internally from joint continuity. -/
theorem cmp102AffinePropagatorJetFTC_hasFDerivAt
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) (x : E) :
    HasFDerivAt
      (cmp102AffinePropagatorJetFTC F n P T v)
      (cmp102AffinePropagatorJetFTCFirstFieldDerivative
        F n P T v x) x := by
  let G : E × ℝ → ℝ := fun p =>
    cmp102PartialPropagatorJet F n (P + p.2 • T) v p.1
  let G' : E × ℝ → E →L[ℝ] ℝ := fun p =>
    cmp102PartialPropagatorJetFieldDerivative
      F n (P + p.2 • T) v p.1
  have hG : Continuous G := by
    exact
      continuous_cmp102PartialPropagatorJet_comp
        F hF n
        (fun p : E × ℝ => P + p.2 • T)
        (fun _p : E × ℝ => v)
        (fun p : E × ℝ => p.1)
        (by fun_prop) (fun _i => by fun_prop) (by fun_prop)
  have hG' : Continuous G' := by
    exact
      continuous_cmp102PartialPropagatorJetFieldDerivative_comp
        F hF n
        (fun p : E × ℝ => P + p.2 • T)
        (fun _p : E × ℝ => v)
        (fun p : E × ℝ => p.1)
        (by fun_prop) (fun _i => by fun_prop) (by fun_prop)
  have hder :=
    hasFDerivAt_intervalIntegral_of_continuous_fieldDerivative
      G G' x hG hG'
      (fun y t =>
        cmp102PartialPropagatorJet_hasFDerivAt
          F hF n (P + t • T) v y)
  simpa [
    cmp102AffinePropagatorJetFTC,
    cmp102AffinePropagatorJetFTCFirstFieldDerivative,
    G, G'] using hder

/-- The second derivative also commutes with the affine FTC integral. -/
theorem
    cmp102AffinePropagatorJetFTCFirstFieldDerivative_hasFDerivAt
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) (x : E) :
    HasFDerivAt
      (cmp102AffinePropagatorJetFTCFirstFieldDerivative F n P T v)
      (cmp102AffinePropagatorJetFTCSecondFieldDerivative
        F n P T v x) x := by
  let G : E × ℝ → E →L[ℝ] ℝ := fun p =>
    cmp102PartialPropagatorJetFieldDerivative
      F n (P + p.2 • T) v p.1
  let G' : E × ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun p =>
    cmp102PartialPropagatorJetSecondFieldDerivative
      F n (P + p.2 • T) v p.1
  have hG : Continuous G := by
    exact
      continuous_cmp102PartialPropagatorJetFieldDerivative_comp
        F hF n
        (fun p : E × ℝ => P + p.2 • T)
        (fun _p : E × ℝ => v)
        (fun p : E × ℝ => p.1)
        (by fun_prop) (fun _i => by fun_prop) (by fun_prop)
  have hG' : Continuous G' := by
    exact
      continuous_cmp102PartialPropagatorJetSecondFieldDerivative_comp
        F hF n
        (fun p : E × ℝ => P + p.2 • T)
        (fun _p : E × ℝ => v)
        (fun p : E × ℝ => p.1)
        (by fun_prop) (fun _i => by fun_prop) (by fun_prop)
  have hder :=
    hasFDerivAt_intervalIntegral_of_continuous_fieldDerivative_banach
      G G' x hG hG'
      (fun y t =>
        cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
          F hF n (P + t • T) v y)
  simpa [
    cmp102AffinePropagatorJetFTCFirstFieldDerivative,
    cmp102AffinePropagatorJetFTCSecondFieldDerivative,
    G, G'] using hder

end GenericAffineJetFTC

/-- First field derivative of one literal complete-domain FTC
contribution. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative
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
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q))) :
    FineField M Q Nc →L[ℝ] ℝ :=
  let Φ :
      RectangularFieldMap M Q Nc × FineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  cmp102AffinePropagatorJetFTCFirstFieldDerivative
    Φ 1 P T (fun _ => Kdomain) A

/-- Second field derivative of one literal complete-domain FTC
contribution. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative
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
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q))) :
    FineField M Q Nc →L[ℝ] FineField M Q Nc →L[ℝ] ℝ :=
  let Φ :
      RectangularFieldMap M Q Nc × FineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  cmp102AffinePropagatorJetFTCSecondFieldDerivative
    Φ 1 P T (fun _ => Kdomain) A

/-- The literal domain FTC contribution is exactly the affine partial-jet
integral generated by its reconstructed domain matrix coefficient. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_affinePropagatorJetFTC
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
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J A Y =
      cmp102AffinePropagatorJetFTC
        (fun p : RectangularFieldMap M Q Nc × FineField M Q Nc =>
          cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
        1 P T
        (fun _ =>
          cmp99PhysicalRectangularOfComplexMatrix
            (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
              anchor K hc hmass hK baseCoarseCovariance
              sigma layerWord choice Y))
        A := by
  unfold cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
    cmp102AffinePropagatorJetFTC
  apply intervalIntegral.integral_congr
  intro t _ht
  exact
    cmp102Eq80PhysicalFineHeadTailDomainCoefficient_eq_partialPropagatorJet
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      sigma hRweak hcap hsmall layerWord choice
      D D₃ V₀ (P + t • T) Δπ J A Y hD hD₃ hV₀

/-- First differentiation under the literal domain FTC integral. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_hasFDerivAt
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
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    HasFDerivAt
      (fun X =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J X Y)
      (cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J A Y) A := by
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
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J X Y) =
        cmp102AffinePropagatorJetFTC
          Φ 1 P T (fun _ => Kdomain) := by
    funext X
    simpa [Φ, Kdomain] using
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_affinePropagatorJetFTC
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J X Y hD hD₃ hV₀
  rw [hfun]
  simpa [
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative,
    Φ, Kdomain] using
    cmp102AffinePropagatorJetFTC_hasFDerivAt
      Φ hΦ 1 P T (fun _ => Kdomain) A

/-- Second differentiation under the literal domain FTC integral. -/
theorem
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative_hasFDerivAt
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
    (J A : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    HasFDerivAt
      (fun X =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J X Y)
      (cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice D D₃ V₀ P T Δπ J A Y) A := by
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
  simpa [
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionFirstFieldDerivative,
    cmp102Eq80PhysicalFineHeadTailDomainFTCContributionSecondFieldDerivative,
    Φ, Kdomain] using
    cmp102AffinePropagatorJetFTCFirstFieldDerivative_hasFDerivAt
      Φ hΦ 1 P T (fun _ => Kdomain) A

section GenericAffineJetFTCContDiff

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The integrated second physical-field derivative is continuous.  This
is the continuity input needed to package the literal affine FTC
contribution as a genuine `C²` function. -/
theorem continuous_cmp102AffinePropagatorJetFTCSecondFieldDerivative
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) :
    Continuous
      (cmp102AffinePropagatorJetFTCSecondFieldDerivative F n P T v) := by
  apply
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
  exact
    continuous_cmp102PartialPropagatorJetSecondFieldDerivative_comp
      F hF n
      (fun p : E × ℝ => P + p.2 • T)
      (fun _p : E × ℝ => v)
      (fun p : E × ℝ => p.1)
      (by fun_prop) (fun _i => by fun_prop) (by fun_prop)

/-- The literal affine propagator-jet FTC contribution is twice
continuously differentiable in the physical field. -/
theorem contDiff_two_cmp102AffinePropagatorJetFTC
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) :
    ContDiff ℝ 2 (cmp102AffinePropagatorJetFTC F n P T v) := by
  have hfirst :
      ContDiff ℝ 1
        (cmp102AffinePropagatorJetFTCFirstFieldDerivative
          F n P T v) :=
    contDiff_one_iff_hasFDerivAt.mpr
      ⟨cmp102AffinePropagatorJetFTCSecondFieldDerivative F n P T v,
        continuous_cmp102AffinePropagatorJetFTCSecondFieldDerivative
          F hF n P T v,
        fun x =>
          cmp102AffinePropagatorJetFTCFirstFieldDerivative_hasFDerivAt
            F hF n P T v x⟩
  have hsecond :
      ContDiff ℝ (1 + 1)
        (cmp102AffinePropagatorJetFTC F n P T v) :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨cmp102AffinePropagatorJetFTCFirstFieldDerivative F n P T v,
        hfirst,
        fun x =>
          cmp102AffinePropagatorJetFTC_hasFDerivAt
            F hF n P T v x⟩
  simpa using hsecond

end GenericAffineJetFTCContDiff

/-- The literal complete-domain FTC contribution is `C²` in the fine
physical field.  All differentiability data are generated from the
source-defined rectangular potential and the reconstructed domain
coefficient. -/
theorem
    contDiff_two_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
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
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ 2
      (fun A =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y) := by
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
      (fun A =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y) =
        cmp102AffinePropagatorJetFTC
          Φ 1 P T (fun _ => Kdomain) := by
    funext A
    simpa [Φ, Kdomain] using
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_affinePropagatorJetFTC
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J A Y hD hD₃ hV₀
  rw [hfun]
  exact contDiff_two_cmp102AffinePropagatorJetFTC
    Φ hΦ 1 P T (fun _ => Kdomain)

end

end YangMills.RG
