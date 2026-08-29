import YangMills.RG.BalabanCMP99Eq342SourceLocalizedCertificateAssembler
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecay
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivative
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjoint
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacian

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact positive-depth C6d CMP99 (3.42) certificate

This is the item-5 per-depth assembler.  It fixes the ambient precision,
coercivity proof, canonical Green, transported background and terminal
spacing internally, then packs the four previously derived action bounds.
Its amplitude and rate still depend on `depth`; it is not the uniform (3.42)
endpoint and does not attain window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification
  (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
variable {U : PhysicalGaugeBackground 4
  (L ^ (depth + 1) * (2 * (K * Q))) Nc}
variable {eta alpha0 alpha1 : ℝ}
variable (OmegaSource : ActiveGaugeRegion 4
  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
variable (R : CMP99Eq335PhysicalRegularityClass
  (L := L ^ (depth + 1)) (N' := 2 * (K * Q))
  (Mlarge := Mlarge) (Nc := Nc) (n := n)
  (scaleExtent := scaleExtent) (S := S)
  (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
variable (C : CMP99SourceRegularCube
  (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q)))) n Mlarge
  scaleExtent S scaleExtent_pos)
variable (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
variable {OmegaPrime0 : ActiveGaugeRegion 4
  (L ^ (depth + 1) * (2 * (K * Q)))}
variable (regions : CMP99SourceActiveRegionChain 4 L
  (L ^ (depth + 1) * (2 * (K * Q)))
  (cmp99Eq360C6dSourceSeparatedAmbientRegion
    (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource) depth)
variable (D : CMP99Eq335Corollary36SourceRegionDictionary
  (cmp99Eq360C6dSourceSeparatedAmbientRegion
    (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
  OmegaPrime0 C)
variable (hL : 2 ≤ L) (halpha1 : alpha1 ≤ 1 / 2)
variable (baselineRadiusBudget : CMP99SourceUbarClosedBudget 4 L Nc depth
  (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))

/-- The four exact positive-depth C6d actions assemble into one per-depth
source-localized Eq. (3.42) certificate. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_perDepthCertificate
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1)
    {decay : ℝ} (hdecay : 0 < decay)
    (root : ActiveGaugeRegion.Site OmegaSource) :
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
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
    let hc := cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
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
    (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
    (OmegaPrime0 := OmegaPrime0)
    R C hscale regions D hL halpha1 baselineRadiusBudget
  let hc := cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
    (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
    (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
    (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1)
    (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
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
  let background := cmp99Eq360C6dSourceSeparatedPhysicalBackground R C hscale
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
    hdepth hsmall
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hgreen : cmp99RegionalDirichletGreen OmegaSource AP hc hAP = G := by
    exact cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_ambient
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall
  have hvalue0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall hdecay root
  have hleft0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_leftDerivative_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall hdecay root
  have hright0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_rightAdjoint_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall hdecay root
  have hlaplacian0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_laplacian_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall hdecay root
  have hvalue : FinitePiLpTypedBlockLocalizedSupBound
      (cmp99RegionalDirichletGreen OmegaSource AP hc hAP)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (valueAmplitude * (ell : ℝ) ^ 2) ownerRate := by
    rw [hgreen]
    simpa [G, ell, A, c, rate, ownerRate, valueAmplitude] using hvalue0
  have hleft : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background ((ell : ℝ) * eta)).comp
        (cmp99RegionalDirichletGreen OmegaSource AP hc hAP))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (leftAmplitude * (ell : ℝ)) ownerRate := by
    rw [hgreen]
    simpa [G, background, ell, A, c, rate, ownerRate, valueAmplitude,
      leftAmplitude] using hleft0
  have hright : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99RegionalDirichletGreen OmegaSource AP hc hAP).comp
        (cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background ((ell : ℝ) * eta)).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (rightAmplitude * (ell : ℝ)) ownerRate := by
    rw [hgreen]
    simpa [G, background, ell, A, c, rate, ownerRate, valueAmplitude,
      rightAmplitude] using hright0
  have hlaplacian : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian OmegaSource
          (matrixSUNAdjointModel Nc) background ((ell : ℝ) * eta)).comp
        (cmp99RegionalDirichletGreen OmegaSource AP hc hAP))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist laplacianAmplitude ownerRate := by
    rw [hgreen]
    simpa [G, background, ell, A, c, rate, ownerRate, valueAmplitude,
      leftAmplitude, laplacianAmplitude] using hlaplacian0
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (depth + 1)
  have hA_nonneg : 0 ≤ A := by
    exact
      (cmp99Eq360C6dSourceSeparatedAmbientPrecision_exponentialKernelBound
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall hdecay).1
  have hc_pos : 0 < c := hc
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    positivity
  have hrate : 0 < rate :=
    finitePiLpExponentialInverseDecayRate_pos hA_nonneg hdecay hrow hc_pos
  have hownerRate : 0 < ownerRate := mul_pos hell hrate
  have hvalueAmplitude : 0 ≤ valueAmplitude := by
    dsimp [valueAmplitude]
    positivity
  have hleftAmplitude : 0 ≤ leftAmplitude := by
    dsimp [leftAmplitude]
    positivity
  have hrightAmplitude : 0 ≤ rightAmplitude := by
    dsimp [rightAmplitude]
    positivity
  have hlaplacianAmplitude : 0 ≤ laplacianAmplitude := by
    dsimp [laplacianAmplitude]
    positivity
  exact cmp99Eq342SourceLocalizedGreenCertificate_of_actionBounds
    hvalueAmplitude hleftAmplitude hrightAmplitude hlaplacianAmplitude
    hownerRate hvalue hleft hright hlaplacian

end

end YangMills.RG
