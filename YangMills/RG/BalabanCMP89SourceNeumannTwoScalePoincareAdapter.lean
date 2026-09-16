import YangMills.RG.BalabanCMP89SourceNeumannQuantitativeOneScalePoincare
import YangMills.RG.BalabanCMP89SourceNeumannTwoLevelPoincareComposition

/-!
# Physical two-scale Neumann Poincare adapter

This adapter fixes both one-step averages, both active regions and both
physical backgrounds before invoking the sealed two-level feedback algebra.
The one-scale Poincare inputs are constructed internally.  The only analytic
input left visible is the Neumann coarse-derivative feedback estimate for the
literal transported average; it is not replaced by the incompatible
zero-extension Dirichlet estimate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N'' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N''] [NeZero Nc]

/-- Physical two-scale specialization of the feedback composition.  The
terminal average is definitionally the printed ordered composition of the
coarse and fine transported source averages. -/
theorem cmp89SourceNeumann_twoScale_quantitativePoincare_of_derivative_feedback
    (Omega : ActiveGaugeRegion d (M * (M * N'')))
    (hOmega : Omega.BlockSaturated)
    (hOmegaC :
      (cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega).BlockSaturated)
    (U : PhysicalGaugeBackground d (M * (M * N'')) Nc)
    (V : PhysicalGaugeBackground d (M * N'') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (derivativeCoeff feedbackCoeff : ℝ)
    (derivativeCoeff_nonneg : 0 ≤ derivativeCoeff)
    (derivative_feedback : ∀ phi,
      ‖cmp89SourceNeumannRegionalCovariantD0CLM
          (cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega)
          (matrixSUNAdjointModel Nc) V ((M : ℝ) * spacing)
          (cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport
              (matrixSUNAdjointModel Nc) U) phi)‖ ^ 2 ≤
        derivativeCoeff *
            ‖cmp89SourceNeumannRegionalCovariantD0CLM
              Omega (matrixSUNAdjointModel Nc) U spacing phi‖ ^ 2 +
          feedbackCoeff * ‖phi‖ ^ 2)
    (feedback_small :
      cmp89SourceNeumannOneScalePoincareConstant d M spacing *
        cmp89SourceNeumannOneScalePoincareConstant d M
          ((M : ℝ) * spacing) * feedbackCoeff < 1) :
    CMP89SourceNeumannRegionalPoincare
      Omega (matrixSUNAdjointModel Nc) U
      ((cmp99SourceTransportedBlockAverageCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega)
          (cmp99SourceWeightedPhysicalTransport
            (matrixSUNAdjointModel Nc) V)).comp
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport
            (matrixSUNAdjointModel Nc) U)))
      spacing
      (cmp89SourceNeumannTwoLevelPoincareConstant
        (cmp89SourceNeumannOneScalePoincareConstant d M spacing)
        (cmp89SourceNeumannOneScalePoincareConstant d M
          ((M : ℝ) * spacing))
        derivativeCoeff feedbackCoeff) := by
  let OmegaC :=
    cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega
  let Qfine := cmp99SourceTransportedBlockAverageCLM Omega
    (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U)
  let Qnext := cmp99SourceTransportedBlockAverageCLM OmegaC
    (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) V)
  have hcoarseSpacing : (M : ℝ) * spacing ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne M)) hspacing
  have hfinePoincare : CMP89SourceNeumannRegionalPoincare
      Omega (matrixSUNAdjointModel Nc) U Qfine spacing
        (cmp89SourceNeumannOneScalePoincareConstant d M spacing) := by
    exact cmp89SourceNeumann_oneScale_quantitativePoincare
      Omega hOmega (matrixSUNAdjointModel Nc) U hspacing
  have hcoarsePoincare : CMP89SourceNeumannRegionalPoincare
      OmegaC (matrixSUNAdjointModel Nc) V Qnext ((M : ℝ) * spacing)
        (cmp89SourceNeumannOneScalePoincareConstant d M
          ((M : ℝ) * spacing)) := by
    exact cmp89SourceNeumann_oneScale_quantitativePoincare
      OmegaC hOmegaC (matrixSUNAdjointModel Nc) V hcoarseSpacing
  apply cmp89SourceNeumannRegionalPoincare_twoLevel_of_derivative_feedback
    (OmegaFine := Omega) (OmegaCoarse := OmegaC)
    (rho := matrixSUNAdjointModel Nc) (UFine := U) (UCoarse := V)
    (Qfine := Qfine) (Qnext := Qnext)
    (fineSpacing := spacing) (coarseSpacing := (M : ℝ) * spacing)
    (fineCoeff := cmp89SourceNeumannOneScalePoincareConstant d M spacing)
    (coarseCoeff := cmp89SourceNeumannOneScalePoincareConstant d M
      ((M : ℝ) * spacing))
    (derivativeCoeff := derivativeCoeff) (feedbackCoeff := feedbackCoeff)
  · exact (cmp89SourceNeumannOneScalePoincareConstant_pos spacing).le
  · exact
      (cmp89SourceNeumannOneScalePoincareConstant_pos
        ((M : ℝ) * spacing)).le
  · exact derivativeCoeff_nonneg
  · exact hfinePoincare
  · exact hcoarsePoincare
  · simpa only [OmegaC, Qfine, Qnext] using derivative_feedback
  · exact feedback_small

end

end YangMills.RG
