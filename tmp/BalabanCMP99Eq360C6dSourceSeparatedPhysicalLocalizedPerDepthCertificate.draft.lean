import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenPerDepthCertificate
import YangMills.RG.BalabanCMP99SourcePhysicalLocalizedRegionRoot

/-!
# Draft: positive-depth physical-localized C6d Eq. (3.42) certificate

PRE-VALIDATION DRAFT: this file is outside the project import graph; its
`.olean` has not been materialized and no compiler or axiom verdict is
claimed.

This wrapper removes the free regional root.  Its region and root are both
constructed from the literal proof-carrying CMP116 localization index.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Mlarge Nc n depth lieDim : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Mlarge] [NeZero Nc]
variable [NeZero lieDim]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification
  (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
variable {U : PhysicalGaugeBackground 4
  (L ^ (depth + 1) * (2 * (K * Q))) Nc}
variable {eta alpha0 alpha1 : ℝ}

/-- The positive-depth C6d certificate on the literal physical localization
carrier.  The root used by the lower assembler is selected internally from
`Z0.2`; it is not a parameter of this theorem. -/
theorem cmp99Eq360C6dSourceSeparatedPhysicalLocalized_perDepthCertificate
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      Nc 4 L lieDim)
    (Z0 : CMP116SourcePhysicalLocalizedRegion Dict)
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q))
      (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube
      (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n Mlarge
      scaleExtent S scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {OmegaPrime0 : ActiveGaugeRegion 4
      (L ^ (depth + 1) * (2 * (K * Q)))}
    (regions : CMP99SourceActiveRegionChain 4 L
      (L ^ (depth + 1) * (2 * (K * Q)))
      (cmp99Eq360C6dSourceSeparatedAmbientRegion
        (cmp99SourcePhysicalLocalizedActiveRegion Dict Z0)) depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary
      (cmp99Eq360C6dSourceSeparatedAmbientRegion
        (cmp99SourcePhysicalLocalizedActiveRegion Dict Z0))
      OmegaPrime0 C)
    (hL : 2 ≤ L) (halpha1 : alpha1 ≤ 1 / 2)
    (baselineRadiusBudget : CMP99SourceUbarClosedBudget 4 L Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1)
    {decay : ℝ} (hdecay : 0 < decay) :
    let OmegaSource := cmp99SourcePhysicalLocalizedActiveRegion Dict Z0
    let root := cmp99SourcePhysicalLocalizedRoot Dict Z0
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
    let ell := L ^ (depth + 1)
    let A := cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget decay
    let c := cmp99Eq360C6dSourceBaselinePhysicalCoercivity
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
    let hc := cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall
    let AP := cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
    let hAP := isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let valueAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let leftAmplitude := valueAmplitude *
      ((1 + Real.exp ownerRate) / eta)
    let rightAmplitude := 648 * valueAmplitude * Real.exp ownerRate / eta
    let laplacianAmplitude := 4 * leftAmplitude *
      ((1 + Real.exp ownerRate) / eta)
    let B0 := cmp99Eq342CommonAmplitude valueAmplitude leftAmplitude
      rightAmplitude laplacianAmplitude
    CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      depth OmegaSource (matrixSUNAdjointModel Nc)
      (cmp99Eq360C6dSourceSeparatedPhysicalBackground R C hscale)
      ((ell : ℝ) * eta) AP c hc hAP B0 ownerRate := by
  dsimp only
  exact cmp99Eq360C6dSourceSeparatedAmbientGreen_perDepthCertificate
    (OmegaSource := cmp99SourcePhysicalLocalizedActiveRegion Dict Z0)
    R C hscale regions D hL halpha1 baselineRadiusBudget
    hdepth hsmall hdecay (cmp99SourcePhysicalLocalizedRoot Dict Z0)

end

end YangMills.RG
