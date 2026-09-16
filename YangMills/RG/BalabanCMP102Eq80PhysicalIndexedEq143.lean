/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CenteredConditionedEq80PartialPotential
import YangMills.RG.BalabanCMP102Eq80CouplingScaledEq143SourceMetric
import YangMills.RG.BalabanCMP116QuadraticCoreHessian

/-!
# The indexed physical equation-(80) core satisfies equation (1.43)

The direct equation-(80) activity is stored as its fixed projected Hessian
plus its total Taylor residual.  Subtracting that same residual leaves the
literal quadratic core.  This file first identifies that core exactly with
one half of the diagonal of the projected coupling-scaled Hessian, and then
feeds the physical CMP102 source-metric producer through that identity.

There is no free pointwise equation-(1.43) hypothesis and no Hessian bound is
stored in the adapter.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev IndexedEq143FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev IndexedEq143CoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev IndexedEq143RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  IndexedEq143CoarseField Q Nc →L[ℝ]
    IndexedEq143FineField M Q Nc

/-- Exact scalar identification of the indexed direct quadratic core.  The
Taylor residual cancels algebraically; the remaining projected Riesz
operator represents the coupling-scaled source Hessian at zero. -/
theorem cmp116Eq142PhysicalQuadraticCore_indexedContour_eq_half_projectedHessian
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : IndexedEq143FineField M Q Nc →L[ℝ]
      IndexedEq143FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      IndexedEq143CoarseField Q Nc →L[ℝ]
        IndexedEq143CoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : IndexedEq143FineField M Q Nc →
      IndexedEq143CoarseField Q Nc)
    (V₀ : IndexedEq143FineField M Q Nc → ℝ)
    (Pprop T : IndexedEq143RectangularFieldMap M Q Nc)
    (Δπ : IndexedEq143FineField M Q Nc →L[ℝ]
      IndexedEq143FineField M Q Nc)
    (J : IndexedEq143FineField M Q Nc)
    (gk : ℝ) (B : IndexedEq143FineField M Q Nc) :
    let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
    let f : IndexedEq143FineField M Q Nc → ℝ := fun A =>
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
        layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
    let PY := physicalBondProjection (Nc := Nc) Y.bondSupport
    cmp116Eq142PhysicalQuadraticCore
        (cmp102Eq80PhysicalIndexedContourTotal
          anchor domains contourCarrier e K hc hmass hK
          baseCoarseCovariance sigma layerWord choice
          D D₃ V₀ Pprop T Δπ J gk)
        (fun j =>
          cmp102Eq80PhysicalIndexedContourResidual
            anchor domains contourCarrier e j K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T Δπ J gk)
        i B =
      (1 / 2 : ℝ) *
        cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0
          (PY B) (PY B) := by
  dsimp only
  let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
    (M := M) anchor domains i
  let f : IndexedEq143FineField M Q Nc → ℝ := fun A =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
  let PY : IndexedEq143FineField M Q Nc →L[ℝ]
      IndexedEq143FineField M Q Nc :=
    physicalBondProjection (Nc := Nc) Y.bondSupport
  unfold cmp116Eq142PhysicalQuadraticCore
  unfold cmp102Eq80PhysicalIndexedContourTotal
  unfold cmp116Eq142PhysicalPotentialTerm
  change
    ((1 / 2 : ℝ) * inner ℝ B
        (PY ((cmp102Eq80CouplingScaledFixedHessian gk f) (PY B))) +
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk B) -
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk B = _
  rw [sub_eq_iff_eq_add]
  rw [PhysicalGaugeCMP116Dictionary.inner_physicalBondProjection_right_eq_left]
  rw [real_inner_comm]
  rw [cmp102Eq80CouplingScaledFixedHessian]
  rw [inner_realBilinearRiesz]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- The indexed direct quadratic core satisfies the literal equation-(1.43)
bound.  The Hessian estimate is produced internally from the physical CMP102
jets and walk ratios at the fixed center `0`; the only extra scalar sign used
below is the already visible nonnegativity of `C3 * epsilon1`. -/
theorem abs_cmp116FDerivHessian_cmp116Eq142PhysicalQuadraticCore_indexedContour_le_eq143
    {nDelta M Q Nc R Delta n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (deltaRadius : Fin nDelta → ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hradiusCap : ∀ j, 1 + deltaRadius j ≤ radius)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : IndexedEq143FineField M Q Nc →L[ℝ]
      IndexedEq143FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      IndexedEq143CoarseField Q Nc →L[ℝ]
        IndexedEq143CoarseField Q Nc)
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts : Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (sigma : Fin nDelta → ℂ)
    (hsigma : CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma)
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho (1 + radius)‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : IndexedEq143FineField M Q Nc →
      IndexedEq143CoarseField Q Nc)
    (V₀ : IndexedEq143FineField M Q Nc → ℝ)
    (Pprop T : IndexedEq143RectangularFieldMap M Q Nc)
    (DeltaPi : IndexedEq143FineField M Q Nc →L[ℝ]
      IndexedEq143FineField M Q Nc)
    (J : IndexedEq143FineField M Q Nc)
    (gk : ℝ)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
    (hsourceJetBound0 : 0 ≤ sourceJetBound)
    (hC : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j, j ≤ 3 →
      ‖iteratedFDeriv ℝ j V₀
        (cmp102Eq80JointRemainderInner D
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : IndexedEq143FineField M Q Nc)))‖ ≤ C)
    (hRjet : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j,
      1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j
          (fun q : IndexedEq143RectangularFieldMap M Q Nc ×
              IndexedEq143FineField M Q Nc => q.2)
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : IndexedEq143FineField M Q Nc))‖ +
        cmp102Eq80JointEvaluationJetMajorant D j
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : IndexedEq143FineField M Q Nc)) ≤
          Rjet ^ j)
    (hsourceJet : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ DeltaPi J 3
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk (0 : IndexedEq143FineField M Q Nc))
          C Rjet ≤ sourceJetBound)
    {cardRatio metricRatio summationRatio : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate (1 + radius) ≤
        cardRatio * (metricRatio * summationRatio))
    (Msource : ℕ) (kappa1 C3 epsilon1 C2 : ℝ)
    (hamplitude : 0 ≤ C3 * epsilon1)
    (hcardRate : 0 ≤ cmp102Eq80Eq143CardRate Msource kappa1)
    (hmetricRate : 0 ≤ cmp102Eq80Eq143MetricRate kappa1)
    (hcardDecay :
      cardRatio ≤ Real.exp
        (-(cmp102Eq80Eq143CardRate Msource kappa1 * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq143MetricRate kappa1 * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Delta : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80CouplingScaledEq143ProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Delta Msource gk kappa1 C3 epsilon1 C2)
    (B A A' : IndexedEq143FineField M Q Nc) (s : ℝ) :
    let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
    |cmp116FDerivHessian
        (cmp116Eq142PhysicalQuadraticCore
          (cmp102Eq80PhysicalIndexedContourTotal
            anchor domains contourCarrier e K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T DeltaPi J gk)
          (fun j =>
            cmp102Eq80PhysicalIndexedContourResidual
              anchor domains contourCarrier e j K hc hmass hK
              baseCoarseCovariance sigma layerWord choice
              D D₃ V₀ Pprop T DeltaPi J gk)
          i)
        (s • B) A' A| ≤
      cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
        (cmp116CubeEdgeTreeMetric Y : ℝ) Y.blocks.card * ‖A‖ * ‖A'‖ := by
  dsimp only
  let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
    (M := M) anchor domains i
  let restrictedSigma : FinBox 4 (2 * Q) → ℂ :=
    cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma
  let f : IndexedEq143FineField M Q Nc → ℝ := fun X =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      restrictedSigma layerWord choice D D₃ V₀ Pprop T DeltaPi J X Y.blocks
  let PY : IndexedEq143FineField M Q Nc →L[ℝ]
      IndexedEq143FineField M Q Nc :=
    physicalBondProjection (Nc := Nc) Y.bondSupport
  let majorant := cmp116Eq143QMajorant C3 epsilon1 Msource C2 kappa1
    (cmp116CubeEdgeTreeMetric Y : ℝ) Y.blocks.card
  have hRweak : (1 : ℝ) ≤ 1 + radius := by linarith
  have hcap : ∀ d : FinBox 4 (2 * Q), ‖restrictedSigma d‖ ≤ 1 + radius := by
    intro d
    exact norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_global
      contourCarrier e deltaRadius sigma hsigma hradius hradiusCap d
  have hH : ∀ a b : IndexedEq143FineField M Q Nc,
      |cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0 a b| ≤
        majorant * ‖a‖ * ‖b‖ := by
    intro a b
    have hsource :=
      abs_cmp116FDerivHessian_cmp102Eq80CouplingScaledPhysicalDomainFTC_le_eq143
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hDelta hDelta1
        restrictedSigma hRweak hcap hsmallContour layerWord choice
        D D₃ V₀ Pprop T DeltaPi J Y gk
        (0 : IndexedEq143FineField M Q Nc) b a
        hD hD₃ hV₀ C Rjet sourceJetBound hsourceJetBound0
        hC hRjet hsourceJet hcardRatio0 hmetricRatio0 hsummation0
        hsplit Msource kappa1 C3 epsilon1 C2 hcardRate hmetricRate
        hcardDecay hmetricDecay hsmall hbudget
    have hsource' :
        |cmp116FDerivHessian
            (cmp102Eq80CouplingScaledPotential gk f) 0 a b| ≤
          majorant * ‖b‖ * ‖a‖ := by
      simpa [Y, f, restrictedSigma, majorant] using hsource
    calc
      |cmp116FDerivHessian
          (cmp102Eq80CouplingScaledPotential gk f) 0 a b| ≤
          majorant * ‖b‖ * ‖a‖ := hsource'
      _ = majorant * ‖a‖ * ‖b‖ := by ring
  have hmajorant : 0 ≤ majorant := by
    dsimp [majorant, cmp116Eq143QMajorant]
    positivity
  have hP : ‖PY‖ ≤ 1 := by
    simpa [PY] using
      (norm_physicalBondProjection_le_one_anyVolume
        (Nc := Nc) Y.bondSupport)
  have hfun :
      cmp116Eq142PhysicalQuadraticCore
          (cmp102Eq80PhysicalIndexedContourTotal
            anchor domains contourCarrier e K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T DeltaPi J gk)
          (fun j =>
            cmp102Eq80PhysicalIndexedContourResidual
              anchor domains contourCarrier e j K hc hmass hK
              baseCoarseCovariance sigma layerWord choice
              D D₃ V₀ Pprop T DeltaPi J gk)
          i =
        fun X => (1 / 2 : ℝ) *
          cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0
            (PY X) (PY X) := by
    funext X
    simpa [Y, f, PY, restrictedSigma] using
      (cmp116Eq142PhysicalQuadraticCore_indexedContour_eq_half_projectedHessian
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T DeltaPi J gk X)
  rw [hfun]
  exact
    abs_cmp116FDerivHessian_half_projectedBilinearDiagonal_le_of_opNorm_le_one
      (cmp116FDerivHessian (cmp102Eq80CouplingScaledPotential gk f) 0)
      PY (s • B) A' A majorant hmajorant hP hH

end

end YangMills.RG
