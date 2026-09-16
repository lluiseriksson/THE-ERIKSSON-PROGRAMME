/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCombinedEq143
import YangMills.RG.BalabanCMP116CenteredConditionedCombinedEq80PartialPotential

/-!
# Terminal equation (1.43) on the direct/native CMP116 ledger

**VALIDATED INTERMEDIATE BRICK.** This source and its public audit were
materialized from source checkpoint `134a21f0` in one fresh Colab Pro+ clone;
the focal queue, `YangMillsCore`, and the full oracle all exited zero.  The
evidence archive has SHA-256 `589769BC64D24493B0F68F5B0458DB017258919B32C265D8C83FA327487233EC`.

The physical combined equation-(1.43) theorem already derives the direct
Hessian estimate from the literal CMP102 jets and walks and discharges the
native branch from the exactly zero native quadratic core.  This module only
puts that theorem in the field shape consumed by the centered-conditioned
`PreEq136` record:

* the base point is the projected physical coordinate field;
* the two probes are literal single-bond cochains;
* spectator and fluctuation fields retain their terminal types;
* the direct/native metric and cardinality dictionaries remain literal.

No equation-(1.43) estimate, native Hessian estimate, or free kernel bound is
accepted as an input.
-/

namespace YangMills.RG

noncomputable section

private abbrev CombinedTerminalEq143FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CombinedTerminalEq143CoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev CombinedTerminalEq143RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CombinedTerminalEq143CoarseField Q Nc →L[ℝ]
    CombinedTerminalEq143FineField M Q Nc

private abbrev CombinedTerminalEq143Bond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

set_option maxHeartbeats 1400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Terminal-field form of physical equation (1.43) on the canonical
direct/native ledger.  The interval premise is retained because the terminal
record quantifies over radial points; the source theorem is uniform in the
real radial parameter. -/
theorem cmp116CenteredConditionedCombinedEq80_terminal_eq143
    {Index : Type*} {nDelta M Q Nc R Delta n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport :
      Finset (CombinedTerminalEq143Bond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (deltaRadius : Fin nDelta → ℝ)
    (interiorBonds : Finset (CombinedTerminalEq143Bond M Q))
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hradiusCap : ∀ j, 1 + deltaRadius j ≤ radius)
    (K : CombinedTerminalEq143FineField M Q Nc →L[ℝ]
      CombinedTerminalEq143FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CombinedTerminalEq143CoarseField Q Nc →L[ℝ]
        CombinedTerminalEq143CoarseField Q Nc)
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
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho (1 + radius)‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : CombinedTerminalEq143FineField M Q Nc →
      CombinedTerminalEq143CoarseField Q Nc)
    (V₀ : CombinedTerminalEq143FineField M Q Nc → ℝ)
    (Pprop T : CombinedTerminalEq143RectangularFieldMap M Q Nc)
    (DeltaPi : CombinedTerminalEq143FineField M Q Nc →L[ℝ]
      CombinedTerminalEq143FineField M Q Nc)
    (J : CombinedTerminalEq143FineField M Q Nc)
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
              (L := M) gk
                (0 : CombinedTerminalEq143FineField M Q Nc)))‖ ≤ C)
    (hRjet : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j,
      1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j
          (fun q : CombinedTerminalEq143RectangularFieldMap M Q Nc ×
              CombinedTerminalEq143FineField M Q Nc => q.2)
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk
                (0 : CombinedTerminalEq143FineField M Q Nc))‖ +
        cmp102Eq80JointEvaluationJetMajorant D j
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk
                (0 : CombinedTerminalEq143FineField M Q Nc)) ≤
          Rjet ^ j)
    (hsourceJet : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ DeltaPi J 3
          (Pprop + t • T,
            cmp109ConstrainedLinearFluctuation
              (L := M) gk
                (0 : CombinedTerminalEq143FineField M Q Nc))
          C Rjet ≤ sourceJetBound)
    {cardRatio metricRatio summationRatio : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate (1 + radius) ≤
        cardRatio * (metricRatio * summationRatio))
    (kappa1 C3 epsilon1 C2 : ℝ)
    (hamplitude : 0 ≤ C3 * epsilon1)
    (hcardRate : 0 ≤ cmp102Eq80Eq143CardRate M kappa1)
    (hmetricRate : 0 ≤ cmp102Eq80Eq143MetricRate kappa1)
    (hcardDecay :
      cardRatio ≤ Real.exp
        (-(cmp102Eq80Eq143CardRate M kappa1 * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq143MetricRate kappa1 * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Delta : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80CouplingScaledEq143ProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound summationRatio
      layerWord Delta M gk kappa1 C3 epsilon1 C2) :
    ∀ (psi phi : CombinedTerminalEq143Bond M Q → SUNLieCoord Nc)
      (sigma : Fin nDelta → ℂ),
      CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma →
      ∀ b y source target (v w : SUNLieCoord Nc),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |cmp116FDerivHessian
            (cmp116Eq142PhysicalQuadraticCore
              (cmp116CenteredConditionedCombinedEq80PartialTotal
                spectatorSupport fluctuationSupport anchor domains E V
                contourCarrier e K hc hmass hK baseCoarseCovariance
                layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma
                (restrictGlobal spectatorSupport psi)
                (restrictGlobal fluctuationSupport phi))
              (cmp116CenteredConditionedCombinedEq80PartialResidual
                spectatorSupport fluctuationSupport anchor domains E V
                contourCarrier e K hc hmass hK baseCoarseCovariance
                layerWord choice D D₃ V₀ Pprop T DeltaPi J gk sigma
                (restrictGlobal spectatorSupport psi)
                (restrictGlobal fluctuationSupport phi)) y)
            (t • physicalBondProjection interiorBonds
              (cmp116SourcePhysicalCoordinateCochain b))
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) source v)
            (singlePhysicalBondCochain
              (d := 4) (N := M * (2 * Q)) (Nc := Nc) target w)| ≤
              cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
                (cmp116Eq80Lemma1CombinedDomainMetric
                  anchor domains E y : ℝ)
                (cmp116Eq80Lemma1CombinedDomainCard anchor domains E y) *
                  ‖v‖ * ‖w‖ := by
  intro psi phi sigma hsigma b y source target v w t _ht
  rw [cmp116CenteredConditionedCombinedEq80PartialTotal_apply,
    cmp116CenteredConditionedCombinedEq80PartialResidual_apply]
  simpa [norm_singlePhysicalBondCochain, mul_comm, mul_left_comm, mul_assoc] using
    (abs_cmp116FDerivHessian_cmp116Eq80Lemma1CombinedPhysical_le_eq143
      anchor domains E (cmp109Lemma1IndexedSourceResidual E V gk D)
      contourCarrier e deltaRadius radius hradius hradiusCap
      K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hDelta hDelta1
      sigma hsigma hsmallContour layerWord choice D D₃ V₀ Pprop T DeltaPi J
      gk hD hD₃ hV₀ C Rjet sourceJetBound hsourceJetBound0
      hC hRjet hsourceJet hcardRatio0 hmetricRatio0 hsummation0 hsplit
      kappa1 C3 epsilon1 C2 hamplitude hcardRate hmetricRate
      hcardDecay hmetricDecay hsmall hbudget y
      (physicalBondProjection interiorBonds
        (cmp116SourcePhysicalCoordinateCochain b))
      (singlePhysicalBondCochain target w)
      (singlePhysicalBondCochain source v) t)

end

end YangMills.RG
