/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainCoefficientSecondFieldDerivative
import YangMills.RG.BalabanCMP102Eq80SourcePi4ThirdFieldDerivative

/-!
# Third field jet of one literal equation-(80) domain coefficient

This file constructs the third physical-field jet of the same reconstructed
rectangular domain coefficient whose Hessian is used in the source-metric
lane.  The operator is extracted from the literal order-four joint jet of
the four-term equation-(80) potential and the literal reconstructed domain
matrix.

The terminal estimate assumes only component source jets of `D`, `D₃`, and
`V₀` through order four.  It does not assume a third derivative bound for a
completed domain activity and does not claim equation (1.36): the remaining
work is to supply uniform small-field component jets with domain decay and
then assemble the residual on the cutoff support.
-/

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

/-- The third physical-field jet of one complete reconstructed rectangular
domain coefficient. -/
noncomputable def
    cmp102Eq80PhysicalFineHeadTailDomainCoefficientThirdFieldDerivative
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
    FineField M Q Nc [×3]→L[ℝ] ℝ :=
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  cmp102PartialPropagatorJetThirdFieldDerivative
    (fun p : RectangularFieldMap M Q Nc × FineField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
    1 H (fun _ => Kdomain) A

/-- The physical third field jet is bounded by the order-four
source-generated joint potential majorant times the norm of the literal
reconstructed domain matrix. -/
theorem
    norm_cmp102Eq80PhysicalFineHeadTailDomainCoefficientThirdFieldDerivative_le_sourceJets
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
    (hC : ∀ i, i ≤ 4 →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D (H, A))‖ ≤ C)
    (hRjet : ∀ i, 1 ≤ i → i ≤ 4 →
      ‖iteratedFDeriv ℝ i
          (fun q :
              RectangularFieldMap M Q Nc × FineField M Q Nc => q.2)
          (H, A)‖ +
        cmp102Eq80JointEvaluationJetMajorant D i (H, A) ≤ Rjet ^ i) :
    ‖cmp102Eq80PhysicalFineHeadTailDomainCoefficientThirdFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ H Δπ J A Y‖ ≤
      cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 4 (H, A) C Rjet *
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
    norm_cmp102PartialPropagatorJetThirdFieldDerivative_le
      Φ 1 H (fun _ => Kdomain) A
  have hjoint :
      ‖iteratedFDeriv ℝ 4 Φ (H, A)‖ ≤
        cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 4 (H, A) C Rjet := by
    simpa [Φ] using
      norm_iteratedFDeriv_cmp102Eq80JointPotential_le_sourceJetMajorant
        D D₃ V₀ Δπ J hD hD₃ hV₀ 4 (H, A) C Rjet hC hRjet
  calc
    ‖cmp102Eq80PhysicalFineHeadTailDomainCoefficientThirdFieldDerivative
        anchor K hc hmass hK baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ H Δπ J A Y‖ ≤
      ‖iteratedFDeriv ℝ 4 Φ (H, A)‖ * ‖Kdomain‖ := by
        simpa [
          cmp102Eq80PhysicalFineHeadTailDomainCoefficientThirdFieldDerivative,
          Φ, Kdomain] using hraw
    _ ≤ cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J 4 (H, A) C Rjet * ‖Kdomain‖ :=
      mul_le_mul_of_nonneg_right hjoint (norm_nonneg Kdomain)
    _ = _ := by rfl

end

end YangMills.RG
