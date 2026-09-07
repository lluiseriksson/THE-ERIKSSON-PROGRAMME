/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCombesThomas

/-!
# Rectangular transition of the physical CMP99 coarse covariance

The fine Dirichlet space and the coarse active stratum both change at a
consecutive source-region transition.  Consequently the printed difference
of coarse covariances is not an endomorphism subtraction.  This file keeps
the two carrier changes literal and proves the exact rectangular identities.

The defect of the middle operator `Q' G'^2 Q'^dagger` is reduced to the
already physical Green mismatch.  No equality transport between regional
carrier types and no abstract covariance-difference hypothesis is used.
-/

namespace YangMills.RG

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Generic rectangular defect of two middle operators `Q G^2 Qstar`.
The exact formula shows that its only non-commuting input is the rectangular
Green mismatch `Gs R - R Gl`. -/
theorem typedCoarseMiddleDefect_eq_greenMismatch
    {Eₗ Eₛ Fₗ Fₛ : Type*}
    [NormedAddCommGroup Eₗ] [InnerProductSpace ℝ Eₗ]
    [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
    [NormedAddCommGroup Fₗ] [InnerProductSpace ℝ Fₗ]
    [NormedAddCommGroup Fₛ] [InnerProductSpace ℝ Fₛ]
    (Gₗ : Eₗ →L[ℝ] Eₗ) (Gₛ : Eₛ →L[ℝ] Eₛ)
    (Qₗ : Eₗ →L[ℝ] Fₗ) (Qₛ : Eₛ →L[ℝ] Fₛ)
    (Qstarₗ : Fₗ →L[ℝ] Eₗ) (Qstarₛ : Fₛ →L[ℝ] Eₛ)
    (Rfine : Eₗ →L[ℝ] Eₛ) (Rcoarse : Fₗ →L[ℝ] Fₛ)
    (hQ : Qₛ.comp Rfine = Rcoarse.comp Qₗ)
    (hQstar : Rfine.comp Qstarₗ = Qstarₛ.comp Rcoarse) :
    cmp99TypedPrecisionDefect
        (Qₗ.comp (Gₗ.comp (Gₗ.comp Qstarₗ)))
        (Qₛ.comp (Gₛ.comp (Gₛ.comp Qstarₛ))) Rcoarse =
      -Qₛ.comp
        (((Gₛ.comp (Gₛ.comp Rfine - Rfine.comp Gₗ)) +
            ((Gₛ.comp Rfine - Rfine.comp Gₗ).comp Gₗ)).comp Qstarₗ) := by
  apply ContinuousLinearMap.ext
  intro x
  have hQx (z : Eₗ) : Qₛ (Rfine z) = Rcoarse (Qₗ z) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : Eₗ →L[ℝ] Fₛ => T z) hQ
  have hQstarx (z : Fₗ) : Rfine (Qstarₗ z) = Qstarₛ (Rcoarse z) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : Fₗ →L[ℝ] Eₛ => T z) hQstar
  simp only [cmp99TypedPrecisionDefect, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, map_sub, map_add]
  rw [← hQx, ← hQstarx]
  module

/-- The literal coarse restriction, exposed with the bundled terminal-space
types used by the physical one-step towers. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepTerminalRestriction
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    (cmp99OmegaSourcePhysicalOneStepTower Seq
        (cmp99OmegaTransitionIndex r) rho U spacing).TerminalSpace.carrier
      →L[ℝ]
    (cmp99OmegaSourcePhysicalOneStepTower Seq
        (cmp99OmegaTransitionNextIndex r) rho U spacing).TerminalSpace.carrier := by
  change CMP99OmegaRegionalCoarseField (M := M) Seq
      (cmp99OmegaTransitionIndex r) (SUNLieCoord Nc) →L[ℝ]
    CMP99OmegaRegionalCoarseField (M := M) Seq
      (cmp99OmegaTransitionNextIndex r) (SUNLieCoord Nc)
  exact cmp99OmegaCoarseTransitionRestriction (M := M) Seq r

theorem cmp99OmegaSourcePhysicalOneStepQ_terminal_transition
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    (cmp99OmegaSourcePhysicalOneStepQ Seq
      (cmp99OmegaTransitionNextIndex r) rho U).comp
        (cmp99OmegaTransitionRestriction (M := M) Seq r) =
      (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
        Seq r rho U spacing).comp
        (cmp99OmegaSourcePhysicalOneStepQ Seq
          (cmp99OmegaTransitionIndex r) rho U) := by
  change (cmp99OmegaSourcePhysicalOneStepQ Seq
      (cmp99OmegaTransitionNextIndex r) rho U).comp
        (cmp99OmegaTransitionRestriction (M := M) Seq r) =
    (cmp99OmegaCoarseTransitionRestriction (M := M) Seq r).comp
      (cmp99OmegaSourcePhysicalOneStepQ Seq
        (cmp99OmegaTransitionIndex r) rho U)
  exact cmp99OmegaSourcePhysicalOneStepQ_transition Seq r rho U

theorem cmp99OmegaSourcePhysicalOneStepQ_adjoint_terminal_transition
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
        (cmp99OmegaSourcePhysicalOneStepQ Seq
          (cmp99OmegaTransitionIndex r) rho U).adjoint =
      (cmp99OmegaSourcePhysicalOneStepQ Seq
        (cmp99OmegaTransitionNextIndex r) rho U).adjoint.comp
        (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
          Seq r rho U spacing) := by
  change (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
      (cmp99OmegaSourcePhysicalOneStepQ Seq
        (cmp99OmegaTransitionIndex r) rho U).adjoint =
    (cmp99OmegaSourcePhysicalOneStepQ Seq
      (cmp99OmegaTransitionNextIndex r) rho U).adjoint.comp
      (cmp99OmegaCoarseTransitionRestriction (M := M) Seq r)
  exact cmp99SourceTransportedBlockAverage_adjoint_transition Seq r
    (cmp99SourceWeightedPhysicalTransport rho U)

/-- The source-weighted adjoints, rather than the counting adjoints, commute
with the same consecutive restrictions. -/
theorem cmp99OmegaSourcePhysicalOneStep_weightedAdjoint_terminal_transition
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
        (cmp99OmegaSourcePhysicalOneStepTower Seq
          (cmp99OmegaTransitionIndex r) rho U spacing).weightedAdjoint =
      (cmp99OmegaSourcePhysicalOneStepTower Seq
        (cmp99OmegaTransitionNextIndex r) rho U spacing).weightedAdjoint.comp
        (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
          Seq r rho U spacing) := by
  let Qlarge := cmp99OmegaSourcePhysicalOneStepQ Seq
    (cmp99OmegaTransitionIndex r) rho U
  let Qsmall := cmp99OmegaSourcePhysicalOneStepQ Seq
    (cmp99OmegaTransitionNextIndex r) rho U
  let Rfine := cmp99OmegaTransitionRestriction (M := M) Seq r
    (g := SUNLieCoord Nc)
  let Rcoarse := cmp99OmegaSourcePhysicalOneStepTerminalRestriction
    Seq r rho U spacing
  have hadj : Rfine.comp Qlarge.adjoint = Qsmall.adjoint.comp Rcoarse :=
    cmp99OmegaSourcePhysicalOneStepQ_adjoint_terminal_transition
      Seq r rho U spacing
  change Rfine.comp
      (cmp99SourceTransportedBlockWeightedAdjointCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r))
        (cmp99OmegaActiveGaugeRegion_blockSaturated
          (M := M) Seq (cmp99OmegaTransitionIndex r))
        (cmp99SourceWeightedPhysicalTransport rho U)) =
    (cmp99SourceTransportedBlockWeightedAdjointCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r))
      (cmp99OmegaActiveGaugeRegion_blockSaturated
        (M := M) Seq (cmp99OmegaTransitionNextIndex r))
      (cmp99SourceWeightedPhysicalTransport rho U)).comp Rcoarse
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint,
    cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T => T x) hadj
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul] using
      congrArg (fun z => (M : ℝ) ^ 4 • z) hx

/-- Literal rectangular defect of the physical middle operators on two
consecutive source regions. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  cmp99TypedPrecisionDefect
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
      Seq r rho U spacing)

set_option maxHeartbeats 1000000 in
/-- The physical middle defect is exactly generated by the rectangular
Green mismatch. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect_eq_greenMismatch
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
        Seq r rho U hspacing ha =
      -(cmp99OmegaSourcePhysicalOneStepQ Seq
          (cmp99OmegaTransitionNextIndex r) rho U).comp
        ((((cmp99OmegaSourcePhysicalOneStepGreen Seq
              (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
            ((cmp99OmegaSourcePhysicalOneStepGreen Seq
                (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
                (cmp99OmegaTransitionRestriction (M := M) Seq r) -
              (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
                (cmp99OmegaSourcePhysicalOneStepGreen Seq
                  (cmp99OmegaTransitionIndex r) rho U hspacing ha))) +
          (((cmp99OmegaSourcePhysicalOneStepGreen Seq
                (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
              (cmp99OmegaTransitionRestriction (M := M) Seq r) -
            (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
              (cmp99OmegaSourcePhysicalOneStepGreen Seq
                (cmp99OmegaTransitionIndex r) rho U hspacing ha)).comp
            (cmp99OmegaSourcePhysicalOneStepGreen Seq
              (cmp99OmegaTransitionIndex r) rho U hspacing ha))).comp
          (cmp99OmegaSourcePhysicalOneStepTower Seq
            (cmp99OmegaTransitionIndex r) rho U spacing).weightedAdjoint) := by
  unfold cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
  unfold cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
  unfold cmp99SourceTowerCoarseCovarianceMiddle
  rw [cmp99OmegaSourcePhysicalOneStepTower_Qprime,
    cmp99OmegaSourcePhysicalOneStepTower_Qprime]
  exact typedCoarseMiddleDefect_eq_greenMismatch
    (Gₗ := cmp99OmegaSourcePhysicalOneStepGreen Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)
    (Gₛ := cmp99OmegaSourcePhysicalOneStepGreen Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha)
    (Qₗ := cmp99OmegaSourcePhysicalOneStepQ Seq
      (cmp99OmegaTransitionIndex r) rho U)
    (Qₛ := cmp99OmegaSourcePhysicalOneStepQ Seq
      (cmp99OmegaTransitionNextIndex r) rho U)
    (Qstarₗ := (cmp99OmegaSourcePhysicalOneStepTower Seq
      (cmp99OmegaTransitionIndex r) rho U spacing).weightedAdjoint)
    (Qstarₛ := (cmp99OmegaSourcePhysicalOneStepTower Seq
      (cmp99OmegaTransitionNextIndex r) rho U spacing).weightedAdjoint)
    (Rfine := cmp99OmegaTransitionRestriction (M := M) Seq r)
    (Rcoarse := cmp99OmegaSourcePhysicalOneStepTerminalRestriction
      Seq r rho U spacing)
    (cmp99OmegaSourcePhysicalOneStepQ_terminal_transition
      Seq r rho U spacing)
    (cmp99OmegaSourcePhysicalOneStep_weightedAdjoint_terminal_transition
      Seq r rho U spacing)

/-- Literal rectangular mismatch of the printed physical coarse
covariances at a consecutive source transition. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransition
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
      (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
        Seq r rho U spacing) -
    (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
      Seq r rho U spacing).comp
      (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
        (cmp99OmegaTransitionIndex r) rho U hspacing ha)

/-- Exact typed second-resolvent identity for the physical coarse covariance.
The only middle-operator input is the literal defect reduced above to the
Green mismatch. -/
theorem cmp99OmegaSourcePhysicalOneStepCoarseCovariance_transition_resolvent
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransition
        Seq r rho U hspacing ha =
      (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
        (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
        ((cmp99OmegaSourcePhysicalOneStepCoarseMiddleTransitionDefect
            Seq r rho U hspacing ha).comp
          (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
            (cmp99OmegaTransitionIndex r) rho U hspacing ha)) := by
  unfold cmp99OmegaSourcePhysicalOneStepCoarseCovarianceTransition
  exact typedGreen_transition_resolvent
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovariance Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepTerminalRestriction
      Seq r rho U spacing)
    (cmp99OmegaSourcePhysicalOneStepMiddle_comp_coarseCovariance Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepCoarseCovariance_comp_middle Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha)

end

end YangMills.RG
