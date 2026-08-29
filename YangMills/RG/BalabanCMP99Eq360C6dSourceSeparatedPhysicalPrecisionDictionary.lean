import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Exact source-carrier form of the literal C6d precision

The existing ambient C6d producer already identifies its Dirichlet
compression with the literal source gauge precision.  The existing carrier
dictionary already proves that source-region compression is the inverse
reindex of that C6d compression.  This file composes those two named facts.

The result keeps the covariant Laplacian, retained `Qprime` and literal
counting coefficient visible under one isometric reindex.  It accepts no
operator equality from the caller.  A later, separate stencil theorem must
still identify the reindexed Laplacian with the literal source-carrier
Laplacian on the transported physical background; that theorem is not
claimed here.
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

/-- Exact source-facing precision dictionary.  The right-hand side is the
inverse carrier reindex of the literal C6d source precision; its Laplacian,
retained `Qprime` and counting coefficient are all constructed internally.
-/
theorem
    cmp99Eq360C6dSourceSeparatedDirichletPrecision_eq_reindexed_sourceGaugePrecision :
    let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
      (L := L) (K := K) (Q := Q) (depth := depth)
    let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
    let W := R.toCubeWitness C alpha1 hscale
    let T0 := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
      R C hscale regions D hL halpha1 baselineRadiusBudget
    let b := cmp99Eq360C6dSourcePhysicalCountingCoefficient
      R C hscale regions D hL halpha1 baselineRadiusBudget
    cmp99SourceAmbientDirichletPrecision OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision
          (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1)
          (OmegaPrime0 := OmegaPrime0)
          OmegaSource R C hscale regions D hL halpha1
          baselineRadiusBudget) =
      finitePiLpTypedKernelReindex E.symm E.symm
        (cmp99SourceGaugePrecision
          (cmp99ActiveRegionSourceCovariantLaplacian
            (cmp99Eq360C6dSourceSeparatedAmbientRegion
              (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
            (matrixSUNAdjointModel Nc) W.transformedBackground eta)
          T0.Qprime b) := by
  dsimp only
  rw [cmp99Eq360C6dSourceSeparatedDirichletPrecision_eq_pullback
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget]
  unfold cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision
  rw [cmp99RegionalDirichletPrecision_C6dSourceAmbientBaseline_eq
    (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
    (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
    (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1)
    (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
    (OmegaPrime0 := OmegaPrime0)
    R C hscale regions D hL halpha1 baselineRadiusBudget]

end

end YangMills.RG
