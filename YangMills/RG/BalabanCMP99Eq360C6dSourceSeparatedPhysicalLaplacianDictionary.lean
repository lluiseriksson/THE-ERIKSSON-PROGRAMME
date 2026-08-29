import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground
import YangMills.RG.FinitePiLpTypedKernelReindexRectangularAlgebra

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Physical C6d derivative and Laplacian carrier dictionary

The source and C6d site fields are related by the same Step-7b equivalence
used by the ambient precision.  This file lifts it to positive physical
bonds, transports the literal covariant derivative, and then obtains the
Laplacian transport from rectangular adjoint/composition algebra.
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

/-- Positive physical bonds transported by the same Step-7b site map. -/
noncomputable def cmp99Eq360C6dSourceSeparatedPhysicalBondEquiv :
    PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) ≃
      PhysicalBond 4 (L ^ (depth + 1) * (2 * (K * Q))) :=
  Equiv.prodCongr
    (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
      (L := L) (K := K) (Q := Q) (depth := depth))
    (Equiv.refl (Fin 4))

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

/-- The literal C6d covariant derivative pulls back to the literal source
covariant derivative on the named transported background. -/
theorem cmp99Eq360C6dSourceSeparatedCovariantD0_reindex_eq :
    let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
      (L := L) (K := K) (Q := Q) (depth := depth)
    let OmegaTarget := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource
    let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
    let B := cmp99Eq360C6dSourceSeparatedPhysicalBondEquiv
      (L := L) (K := K) (Q := Q) (depth := depth)
    finitePiLpTypedKernelReindex
        (ι := ActiveGaugeRegion.Site OmegaTarget)
        (κ := PhysicalBond 4 (L ^ (depth + 1) * (2 * (K * Q))))
        (ι' := ActiveGaugeRegion.Site OmegaSource)
        (κ' := PhysicalBond 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
        (g := SUNLieCoord Nc) E.symm B.symm
        (cmp99ActiveRegionSourceCovariantD0CLM
          OmegaTarget
          (matrixSUNAdjointModel Nc)
          (R.toCubeWitness C alpha1 hscale).transformedBackground eta) =
      cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
        (matrixSUNAdjointModel Nc)
        (cmp99Eq360C6dSourceSeparatedPhysicalBackground R C hscale) eta := by
  dsimp only
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
  let B := cmp99Eq360C6dSourceSeparatedPhysicalBondEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro bond
  rcases bond with ⟨x, i⟩
  have hext := cmp99GaugeZeroCochainReindex_extendZero e OmegaSource phi
  have hlocalized :
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
          E.symm.symm).toContinuousLinearEquiv phi =
      cmp99ActiveGaugeZeroCochainReindex e OmegaSource phi := by
    simp [E, cmp99ActiveGaugeZeroCochainReindex]
  dsimp only [E, e] at hlocalized
  dsimp only [e] at hext
  have htransported :
      (extendZeroZeroCLM
          (cmp99Eq360C6dSourceSeparatedAmbientRegion
            (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource))
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
              (cmp99ActiveGaugeRegionSiteReindexEquiv
                (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
                  (L := L) (K := K) (Q := Q) (depth := depth))
                OmegaSource).symm.symm).toContinuousLinearEquiv phi) =
        cmp99GaugeZeroCochainReindex
          (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
            (L := L) (K := K) (Q := Q) (depth := depth))
          (extendZeroZeroCLM OmegaSource phi) := by
    rw [hlocalized]
    exact hext.symm
  have hshift := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv_shift
    (L := L) (K := K) (Q := Q) (depth := depth) x i
  have hshift_symm :
      (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
        (L := L) (K := K) (Q := Q) (depth := depth)).symm
          ((cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
            (L := L) (K := K) (Q := Q) (depth := depth) x).shift i) =
        x.shift i := by
    rw [← hshift]
    exact Equiv.symm_apply_apply _ (x.shift i)
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (cmp99Eq360C6dSourceSeparatedPhysicalBondEquiv
        (L := L) (K := K) (Q := Q) (depth := depth)).symm).toContinuousLinearEquiv
  let covDtarget :=
    covariantD0CLM (matrixSUNAdjointModel Nc)
      (R.toCubeWitness C alpha1 hscale).transformedBackground
  have hevaluated :
      (targetMap (eta⁻¹ • covDtarget
        ((extendZeroZeroCLM
          (cmp99Eq360C6dSourceSeparatedAmbientRegion
            (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource))
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
            (cmp99ActiveGaugeRegionSiteReindexEquiv
              (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
                (L := L) (K := K) (Q := Q) (depth := depth))
              OmegaSource).symm.symm).toContinuousLinearEquiv phi)))) (x, i) =
        (targetMap (eta⁻¹ • covDtarget
          (cmp99GaugeZeroCochainReindex
            (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
              (L := L) (K := K) (Q := Q) (depth := depth))
            (extendZeroZeroCLM OmegaSource phi)))) (x, i) := by
    exact congrArg
      (fun z => (targetMap (eta⁻¹ • covDtarget z)) (x, i)) htransported
  simp only [finitePiLpTypedKernelReindex,
    cmp99ActiveRegionSourceCovariantD0CLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  calc
    _ = (targetMap (eta⁻¹ • covDtarget
        (cmp99GaugeZeroCochainReindex
          (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
            (L := L) (K := K) (Q := Q) (depth := depth))
          (extendZeroZeroCLM OmegaSource phi)))) (x, i) := hevaluated
    _ = _ := by
      simp [targetMap, covDtarget, covariantD0CLM_apply,
        cmp99GaugeZeroCochainReindex,
        cmp99Eq360C6dSourceSeparatedPhysicalBondEquiv,
        cmp99Eq360C6dSourceSeparatedPhysicalBackground_apply,
        hshift_symm]

/-- Consequently the inverse reindex of the literal C6d Laplacian is the
literal source-carrier Laplacian on the transported background. -/
theorem cmp99Eq360C6dSourceSeparatedCovariantLaplacian_reindex_eq :
    let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
      (L := L) (K := K) (Q := Q) (depth := depth)
    let OmegaTarget := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource
    let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
    finitePiLpTypedKernelReindex
        (ι := ActiveGaugeRegion.Site OmegaTarget)
        (κ := ActiveGaugeRegion.Site OmegaTarget)
        (ι' := ActiveGaugeRegion.Site OmegaSource)
        (κ' := ActiveGaugeRegion.Site OmegaSource)
        (g := SUNLieCoord Nc) E.symm E.symm
        (cmp99ActiveRegionSourceCovariantLaplacian
          OmegaTarget
          (matrixSUNAdjointModel Nc)
          (R.toCubeWitness C alpha1 hscale).transformedBackground eta) =
      cmp99ActiveRegionSourceCovariantLaplacian OmegaSource
        (matrixSUNAdjointModel Nc)
        (cmp99Eq360C6dSourceSeparatedPhysicalBackground R C hscale) eta := by
  dsimp only
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
  let B := cmp99Eq360C6dSourceSeparatedPhysicalBondEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let Dtarget := cmp99ActiveRegionSourceCovariantD0CLM
    (cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
    (matrixSUNAdjointModel Nc)
    (R.toCubeWitness C alpha1 hscale).transformedBackground eta
  let Dsource := cmp99ActiveRegionSourceCovariantD0CLM OmegaSource
    (matrixSUNAdjointModel Nc)
    (cmp99Eq360C6dSourceSeparatedPhysicalBackground R C hscale) eta
  have hD : finitePiLpTypedKernelReindex E.symm B.symm Dtarget = Dsource :=
    cmp99Eq360C6dSourceSeparatedCovariantD0_reindex_eq
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) OmegaSource R C hscale
  change finitePiLpTypedKernelReindex E.symm E.symm
      (Dtarget.adjoint.comp Dtarget) = Dsource.adjoint.comp Dsource
  calc
    _ = (finitePiLpTypedKernelReindex E.symm B.symm Dtarget).adjoint.comp
        (finitePiLpTypedKernelReindex E.symm B.symm Dtarget) :=
      finitePiLpTypedKernelReindex_adjoint_comp_self E.symm B.symm Dtarget
    _ = Dsource.adjoint.comp Dsource := by rw [hD]

end

end YangMills.RG
