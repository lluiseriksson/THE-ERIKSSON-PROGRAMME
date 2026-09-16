import YangMills.RG.BalabanCMP99Eq342SourceLocalizedCertificateAssembler
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayZeroDepth
import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthActions

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]
variable (OmegaSource : ActiveGaugeRegion 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)))
variable (regions : CMP99SourceActiveRegionChain 4 L
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) OmegaSource 0)
variable (hL : 2 ≤ L)
variable {spacing epsilon : ℝ}
variable (background : GaugeConfig 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) (SUN Nc))
variable (chain : CMP99SourceUbarRadiusChain 4 L Nc 0 epsilon)
variable (fineSmall : ∀ e : ConcreteEdge 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)),
  ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)

/-- The exact depth-zero value and derivative actions assemble into the base
source-localized Eq. (3.42) certificate. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_zeroDepthCertificate
    (hspacing : 0 < spacing)
    {decay : ℝ} (hdecay : 0 < decay)
    (root : ActiveGaugeRegion.Site OmegaSource) :
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
    let ell := L ^ (0 + 1)
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        (OmegaSource := OmegaSource) (spacing := spacing)
        regions hL background chain fineSmall decay
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall
    let hc :=
      cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
        regions (by norm_num : 2 ≤ 4) hL hspacing background chain fineSmall
    let AP := cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall
    let hAP :=
      isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        (OmegaSource := OmegaSource) (spacing := spacing)
        regions hL background chain fineSmall
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
  let ell := L ^ (0 + 1)
  let A :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall decay
  let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    (OmegaSource := OmegaSource) (spacing := spacing)
    regions hL background chain fineSmall
  let hc :=
    cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
      regions (by norm_num : 2 ≤ 4) hL hspacing background chain fineSmall
  let AP := cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    (OmegaSource := OmegaSource) (spacing := spacing)
    regions hL background chain fineSmall
  let hAP :=
    isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall
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
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    (OmegaSource := OmegaSource) (spacing := spacing)
    regions hL background chain fineSmall hspacing
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hgreen : cmp99RegionalDirichletGreen OmegaSource AP hc hAP = G := by
    exact cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_zero
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall hspacing
  have hvalue0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      OmegaSource regions hL background chain fineSmall
      hspacing hdecay root
  have hleft0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_leftDerivative_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      OmegaSource regions hL background chain fineSmall
      hspacing hdecay root
  have hright0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_rightAdjoint_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      OmegaSource regions hL background chain fineSmall
      hspacing hdecay root
  have hlaplacian0 :=
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_laplacian_blockLocalizedSupBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      OmegaSource regions hL background chain fineSmall
      hspacing hdecay root
  have hvalue : FinitePiLpTypedBlockLocalizedSupBound
      (cmp99RegionalDirichletGreen OmegaSource AP hc hAP)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist (valueAmplitude * (ell : ℝ) ^ 2) ownerRate := by
    rw [hgreen]
    simpa [G, ell, A, c, rate, ownerRate, valueAmplitude] using hvalue0
  have hleft : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).comp
        (cmp99RegionalDirichletGreen OmegaSource AP hc hAP))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedBondOwner L K Q 0)
      finBoxDist (leftAmplitude * (ell : ℝ)) ownerRate := by
    rw [hgreen]
    simpa [G, ell, A, c, rate, ownerRate, valueAmplitude,
      leftAmplitude] using hleft0
  have hright : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99RegionalDirichletGreen OmegaSource AP hc hAP).comp
        (cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist (rightAmplitude * (ell : ℝ)) ownerRate := by
    rw [hgreen]
    simpa [G, ell, A, c, rate, ownerRate, valueAmplitude,
      rightAmplitude] using hright0
  have hlaplacian : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).comp
        (cmp99RegionalDirichletGreen OmegaSource AP hc hAP))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist laplacianAmplitude ownerRate := by
    rw [hgreen]
    simpa [G, ell, A, c, rate, ownerRate, valueAmplitude,
      leftAmplitude, laplacianAmplitude] using hlaplacian0
  have hA_nonneg : 0 ≤ A :=
    (cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero_exponentialKernelBound
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall
      hspacing hdecay).1
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    positivity
  have hrate : 0 < rate :=
    finitePiLpExponentialInverseDecayRate_pos hA_nonneg hdecay hrow hc
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (0 + 1)
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
  have hvalue' : FinitePiLpTypedBlockLocalizedSupBound
      (cmp99RegionalDirichletGreen OmegaSource AP hc hAP)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist (valueAmplitude * (L ^ (0 + 1) : ℝ) ^ 2) ownerRate := by
    simpa [ell] using hvalue
  have hleft' : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).comp
        (cmp99RegionalDirichletGreen OmegaSource AP hc hAP))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedBondOwner L K Q 0)
      finBoxDist (leftAmplitude * (L ^ (0 + 1) : ℝ)) ownerRate := by
    simpa [ell] using hleft
  have hright' : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99RegionalDirichletGreen OmegaSource AP hc hAP).comp
        (cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
          (matrixSUNAdjointModel Nc) background spacing).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist (rightAmplitude * (L ^ (0 + 1) : ℝ)) ownerRate := by
    simpa [ell] using hright
  exact cmp99Eq342SourceLocalizedGreenCertificate_of_actionBounds
    (Omega := OmegaSource) (rho := matrixSUNAdjointModel Nc)
    (U := background) (spacing := spacing)
    (A := AP) (c := c) (hc := hc) (hAcoer := hAP)
    (Avalue := valueAmplitude) (Aleft := leftAmplitude)
    (Aright := rightAmplitude) (Alaplacian := laplacianAmplitude)
    (rate := ownerRate)
    hvalueAmplitude hleftAmplitude hrightAmplitude hlaplacianAmplitude
    hownerRate hvalue' hleft' hright' hlaplacian

end

end YangMills.RG
