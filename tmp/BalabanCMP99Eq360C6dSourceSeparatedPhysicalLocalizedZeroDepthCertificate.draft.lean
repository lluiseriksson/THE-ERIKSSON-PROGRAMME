import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthCertificate
import YangMills.RG.BalabanCMP99SourcePhysicalLocalizedRegionRoot

/-!
# Draft: zero-depth physical-localized C6d Eq. (3.42) certificate

PRE-VALIDATION DRAFT: this file is outside the project import graph; its
`.olean` has not been materialized and no compiler or axiom verdict is
claimed.

The base branch remains separate from the positive-depth retained tower.  Its
regional root is constructed internally from the literal CMP116 localization
index.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc lieDim : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc] [NeZero lieDim]

/-- The exact depth-zero source-localized certificate without a caller-visible
regional root. -/
theorem cmp99Eq360C6dSourceSeparatedPhysicalLocalized_zeroDepthCertificate
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q))
      Nc 4 L lieDim)
    (Z0 : CMP116SourcePhysicalLocalizedRegion Dict)
    (regions : CMP99SourceActiveRegionChain 4 L
      (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q))
      (cmp99SourcePhysicalLocalizedActiveRegion Dict Z0) 0)
    (hL : 2 ≤ L)
    {spacing epsilon : ℝ}
    (background : GaugeConfig 4
      (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hspacing : 0 < spacing)
    {decay : ℝ} (hdecay : 0 < decay) :
    let OmegaSource := cmp99SourcePhysicalLocalizedActiveRegion Dict Z0
    let root := cmp99SourcePhysicalLocalizedRoot Dict Z0
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
    let ell := L ^ (0 + 1)
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) regions hL background chain fineSmall decay
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (Nc := Nc) regions hL background chain fineSmall
    let hc :=
      cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
        regions (by norm_num : 2 ≤ 4) hL hspacing background chain fineSmall
    let AP := cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
      (Nc := Nc) regions hL background chain fineSmall
    let hAP :=
      isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
        (Nc := Nc) regions hL background chain fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let valueAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let leftAmplitude := valueAmplitude * (ell : ℝ) *
      ((1 + Real.exp ownerRate) / spacing)
    let rightAmplitude := 648 * valueAmplitude * Real.exp ownerRate *
      (ell : ℝ) / spacing
    let laplacianAmplitude := 4 * leftAmplitude * (ell : ℝ) *
      ((1 + Real.exp ownerRate) / spacing)
    let B0 := cmp99Eq342CommonAmplitude valueAmplitude leftAmplitude
      rightAmplitude laplacianAmplitude
    CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      0 OmegaSource (matrixSUNAdjointModel Nc) background spacing
      AP c hc hAP B0 ownerRate := by
  dsimp only
  exact cmp99Eq360C6dSourceSeparatedAmbientGreen_zeroDepthCertificate
    (OmegaSource := cmp99SourcePhysicalLocalizedActiveRegion Dict Z0)
    regions hL background chain fineSmall hspacing hdecay
    (cmp99SourcePhysicalLocalizedRoot Dict Z0)

end

end YangMills.RG
