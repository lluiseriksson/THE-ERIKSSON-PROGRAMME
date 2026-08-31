import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision
import YangMills.RG.BalabanCMP89SourceNeumannTwoLevelPoincareAlgebra

/-!
# Regional two-level Neumann Poincare composition

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

This adapter packages the sealed two-level feedback algebra as the literal
regional Poincare proposition consumed by the CMP89 Neumann precision.  The
four maps remain explicit and separately typed.  No generated-background or
retained-tower dictionary is inferred here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d Nfine Ncoarse Nc : ℕ}
  [NeZero d] [NeZero Nfine] [NeZero Ncoarse] [NeZero Nc]

/-- A deliberately explicit common coefficient dominating the fine-energy
and terminal-average coefficients after feedback absorption. -/
noncomputable def cmp89SourceNeumannTwoLevelPoincareConstant
    (fineCoeff coarseCoeff derivativeCoeff feedbackCoeff : ℝ) : ℝ :=
  (fineCoeff * (1 + coarseCoeff * derivativeCoeff) +
      fineCoeff * coarseCoeff) /
    (1 - fineCoeff * coarseCoeff * feedbackCoeff)

/-- Compose fine and coarse regional Poincare estimates through an explicit
coarse-derivative feedback inequality.  The terminal averaging operator in
the conclusion is definitionally the composition `Qnext.comp Qfine`. -/
theorem cmp89SourceNeumannRegionalPoincare_twoLevel_of_derivative_feedback
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (OmegaFine : ActiveGaugeRegion d Nfine)
    (OmegaCoarse : ActiveGaugeRegion d Ncoarse)
    (rho : SUNAdjointModel Nc)
    (UFine : PhysicalGaugeBackground d Nfine Nc)
    (UCoarse : PhysicalGaugeBackground d Ncoarse Nc)
    (Qfine : ActiveGaugeZeroCochain OmegaFine (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaCoarse (SUNLieCoord Nc))
    (Qnext : ActiveGaugeZeroCochain OmegaCoarse (SUNLieCoord Nc) →L[ℝ] F)
    (fineSpacing coarseSpacing : ℝ)
    (fineCoeff coarseCoeff derivativeCoeff feedbackCoeff : ℝ)
    (fineCoeff_nonneg : 0 ≤ fineCoeff)
    (coarseCoeff_nonneg : 0 ≤ coarseCoeff)
    (derivativeCoeff_nonneg : 0 ≤ derivativeCoeff)
    (finePoincare : CMP89SourceNeumannRegionalPoincare
      OmegaFine rho UFine Qfine fineSpacing fineCoeff)
    (coarsePoincare : CMP89SourceNeumannRegionalPoincare
      OmegaCoarse rho UCoarse Qnext coarseSpacing coarseCoeff)
    (derivative_feedback : ∀ phi,
      ‖cmp89SourceNeumannRegionalCovariantD0CLM
          OmegaCoarse rho UCoarse coarseSpacing (Qfine phi)‖ ^ 2 ≤
        derivativeCoeff *
            ‖cmp89SourceNeumannRegionalCovariantD0CLM
              OmegaFine rho UFine fineSpacing phi‖ ^ 2 +
          feedbackCoeff * ‖phi‖ ^ 2)
    (feedback_small : fineCoeff * coarseCoeff * feedbackCoeff < 1) :
    CMP89SourceNeumannRegionalPoincare
      OmegaFine rho UFine (Qnext.comp Qfine) fineSpacing
      (cmp89SourceNeumannTwoLevelPoincareConstant
        fineCoeff coarseCoeff derivativeCoeff feedbackCoeff) := by
  intro phi
  let DFine := cmp89SourceNeumannRegionalCovariantD0CLM
    OmegaFine rho UFine fineSpacing
  let DCoarse := cmp89SourceNeumannRegionalCovariantD0CLM
    OmegaCoarse rho UCoarse coarseSpacing
  have hexact := norm_sq_le_twoLevelPoincare_of_derivative_feedback
    (fineDerivative := DFine) (fineAverage := Qfine)
    (coarseDerivative := DCoarse) (terminalAverage := Qnext)
    fineCoeff coarseCoeff derivativeCoeff feedbackCoeff
    fineCoeff_nonneg coarseCoeff_nonneg finePoincare coarsePoincare
    derivative_feedback feedback_small phi
  have hden : 0 < 1 - fineCoeff * coarseCoeff * feedbackCoeff :=
    sub_pos.mpr feedback_small
  have hfineWeight :
      0 ≤ fineCoeff * (1 + coarseCoeff * derivativeCoeff) :=
    mul_nonneg fineCoeff_nonneg
      (add_nonneg zero_le_one
        (mul_nonneg coarseCoeff_nonneg derivativeCoeff_nonneg))
  have hterminalWeight : 0 ≤ fineCoeff * coarseCoeff :=
    mul_nonneg fineCoeff_nonneg coarseCoeff_nonneg
  calc
    ‖phi‖ ^ 2 ≤
        (fineCoeff * (1 + coarseCoeff * derivativeCoeff) * ‖DFine phi‖ ^ 2 +
            fineCoeff * coarseCoeff * ‖Qnext (Qfine phi)‖ ^ 2) /
          (1 - fineCoeff * coarseCoeff * feedbackCoeff) := hexact
    _ ≤ cmp89SourceNeumannTwoLevelPoincareConstant
          fineCoeff coarseCoeff derivativeCoeff feedbackCoeff *
        (‖DFine phi‖ ^ 2 + ‖(Qnext.comp Qfine) phi‖ ^ 2) := by
      simp only [cmp89SourceNeumannTwoLevelPoincareConstant,
        ContinuousLinearMap.comp_apply]
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hden).2
      have hD : 0 ≤ ‖DFine phi‖ ^ 2 := sq_nonneg _
      have hQ : 0 ≤ ‖Qnext (Qfine phi)‖ ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hfineWeight hQ,
        mul_nonneg hterminalWeight hD]

end

end YangMills.RG
