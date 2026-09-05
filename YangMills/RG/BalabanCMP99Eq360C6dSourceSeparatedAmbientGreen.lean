import YangMills.RG.BalabanCMP99ActiveGaugeRegionReindexGreen
import YangMills.RG.BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Mlarge] [NeZero Nc]

private instance instNeZeroEq360C6dSourceSeparatedLargeBlockSide
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth) :=
  ⟨(Nat.mul_pos (NeZero.pos K)
    (pow_pos (NeZero.pos L) (depth + 1))).ne'⟩

private instance instNeZeroEq360C6dSourceSeparatedAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- The one named source-to-C6d full-site equivalence.  Its implementation
already contains the source theorem
`cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier`; this alias keeps
that convention visible at the source-facing endpoint. -/
noncomputable def cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv :
    FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) ≃
      FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) :=
  cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth

/-- Transport the literal source region to the carrier on which the C6d
ambient producer is instantiated. -/
noncomputable def cmp99Eq360C6dSourceSeparatedAmbientRegion
    (OmegaSource : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ActiveGaugeRegion 4 (L ^ (depth + 1) * (2 * (K * Q))) :=
  cmp99ActiveGaugeRegionReindex
    (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
      (L := L) (K := K) (Q := Q) (depth := depth)) OmegaSource

/-- Pulling the transported region back through the named inverse recovers
the source region.  This is a theorem, not a definitional carrier
identification. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientRegion_symm_eq
    (OmegaSource : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99ActiveGaugeRegionReindex
        (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
          (L := L) (K := K) (Q := Q) (depth := depth)).symm
        (cmp99Eq360C6dSourceSeparatedAmbientRegion
          (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource) =
      OmegaSource := by
  exact cmp99ActiveGaugeRegionReindex_symm_reindex_eq
    (cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
      (L := L) (K := K) (Q := Q) (depth := depth)) OmegaSource

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

/-- The literal C6d ambient precision on the transported region.  The fine
factor, residual side and retained-tower ratio are fixed internally to
`L^(depth+1)`, `2*(K*Q)` and `L`, respectively. -/
noncomputable def cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision :
    GaugeZeroCochain 4 (L ^ (depth + 1) * (2 * (K * Q)))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (L ^ (depth + 1) * (2 * (K * Q)))
        (SUNLieCoord Nc) :=
  cmp99Eq360C6dSourceAmbientBaselinePrecision
    (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
    (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
    (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1)
    (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
    (OmegaPrime0 := OmegaPrime0)
    R C hscale regions D hL halpha1 baselineRadiusBudget

/-- Pull the one C6d ambient precision back to the source-separated carrier.
No source ambient operator is supplied by the caller. -/
noncomputable def cmp99Eq360C6dSourceSeparatedAmbientPrecision :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  finitePiLpTypedKernelReindex e.symm e.symm
    (cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget)

/-- On the literal source-separated carrier, the older CMP99 regional
Dirichlet precision and the generic ambient Dirichlet compression are the
same restriction/precision/extension sandwich.  The equality is named so
the Eq. (3.42) consumer never relies on an implicit notation change. -/
theorem cmp99Eq360C6dSourceSeparatedRegionalDirichletPrecision_eq_ambient :
    cmp99RegionalDirichletPrecision
        (M := cmp99SourceSeparatedLargeBlockSide L K depth) (Q := Q)
        OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision
          (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1)
          (OmegaPrime0 := OmegaPrime0)
          OmegaSource R C hscale regions D hL halpha1
          baselineRadiusBudget) =
      cmp99SourceAmbientDirichletPrecision OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision
          (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1)
          (OmegaPrime0 := OmegaPrime0)
          OmegaSource R C hscale regions D hL halpha1
          baselineRadiusBudget) := by
  rfl

/-- Coercivity of the pulled-back source ambient precision is transported
from the internally generated C6d ambient producer. -/
theorem isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    IsCoerciveCLM
      (cmp99Eq360C6dSourceSeparatedAmbientPrecision
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget)
      (cmp99Eq360C6dSourceBaselinePhysicalCoercivity
        (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
        (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
        (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1)
        (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
          (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
        (OmegaPrime0 := OmegaPrime0)
        R C hscale regions D hL halpha1 baselineRadiusBudget) := by
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  exact isCoerciveCLM_finitePiLpTypedKernelReindex e.symm
    (cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget)
    (isCoerciveCLM_cmp99Eq360C6dSourceAmbientBaselinePrecision
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)

/-- Exact inverse-orientation compression dictionary.  The forward ambient
reindex cancels only through the named reindex theorem; the active-region
carrier is transported explicitly. -/
theorem cmp99Eq360C6dSourceSeparatedDirichletPrecision_eq_pullback
    :
    let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
      (L := L) (K := K) (Q := Q) (depth := depth)
    let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
    let Kc6d := cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
    cmp99SourceAmbientDirichletPrecision OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision
          (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
          OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget) =
      finitePiLpTypedKernelReindex E.symm E.symm
        (cmp99SourceAmbientDirichletPrecision
          (cmp99Eq360C6dSourceSeparatedAmbientRegion
            (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
          Kc6d) := by
  dsimp only
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let Kc6d := cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
  let Ksource := finitePiLpTypedKernelReindex e.symm e.symm Kc6d
  have hforward : finitePiLpTypedKernelReindex e e Ksource = Kc6d := by
    exact finitePiLpTypedKernelReindex_symm_reindex e.symm Kc6d
  have hcompression :=
    finitePiLpTypedKernelReindex_symm_sourceAmbientDirichletPrecision
      e OmegaSource Ksource
  rw [hforward] at hcompression
  exact hcompression.symm

/-- Canonical source Green generated from the one pulled-back ambient
precision. -/
noncomputable def cmp99Eq360C6dSourceSeparatedAmbientGreen
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) :=
  cmp99SourceAmbientDirichletGreen OmegaSource
    (cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget)
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)
    (isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall)

/-- The Eq. (3.42) regional-Green notation denotes the same canonical
inverse as the generic source ambient Green on this exact carrier.  Both
objects are generated internally from the one transported ambient precision;
no Green equality is caller data. -/
theorem cmp99Eq360C6dSourceSeparatedRegionalDirichletGreen_eq_ambient
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    cmp99RegionalDirichletGreen
        (M := cmp99SourceSeparatedLargeBlockSide L K depth) (Q := Q)
        OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision
          (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1)
          (OmegaPrime0 := OmegaPrime0)
          OmegaSource R C hscale regions D hL halpha1
          baselineRadiusBudget)
        (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
          (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
          (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
          (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1)
          (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
            (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
          (OmegaPrime0 := OmegaPrime0)
          R C hscale regions D hL halpha1 baselineRadiusBudget
          hdepth R.eta_pos hsmall)
        (isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
          (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1)
          (OmegaPrime0 := OmegaPrime0)
          OmegaSource R C hscale regions D hL halpha1
          baselineRadiusBudget hdepth hsmall) =
      cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall := by
  unfold cmp99RegionalDirichletGreen
    cmp99Eq360C6dSourceSeparatedAmbientGreen
    cmp99SourceAmbientDirichletGreen
  simp only [
    cmp99Eq360C6dSourceSeparatedRegionalDirichletPrecision_eq_ambient]

/-- The source-separated Dirichlet precision is a left inverse of the
internally generated source Green.  This is the exact inverse identity used
by the subsequent regional-defect construction; it is not supplied by the
caller. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientPrecision_comp_green
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    (cmp99SourceAmbientDirichletPrecision OmegaSource
      (cmp99Eq360C6dSourceSeparatedAmbientPrecision
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1
        baselineRadiusBudget)).comp
      (cmp99Eq360C6dSourceSeparatedAmbientGreen
        (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
        OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
        hdepth hsmall) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)) := by
  exact cmp99SourceAmbientDirichletPrecision_comp_green
    OmegaSource
    (cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget)
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)
    (isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall)

/-- The internally generated source Green is also a left inverse of the
source-separated Dirichlet precision. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_comp_precision
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    (cmp99Eq360C6dSourceSeparatedAmbientGreen
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall).comp
      (cmp99SourceAmbientDirichletPrecision OmegaSource
        (cmp99Eq360C6dSourceSeparatedAmbientPrecision
          (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1)
          (OmegaPrime0 := OmegaPrime0)
          OmegaSource R C hscale regions D hL halpha1
          baselineRadiusBudget)) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)) := by
  exact cmp99SourceAmbientDirichletGreen_comp_precision
    OmegaSource
    (cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget)
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)
    (isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall)

/-- The source Green inherits the inverse-coercivity operator-norm bound.
The bound is expressed using the same physical coercivity constant that is
transported with the source precision. -/
theorem norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_le
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    ‖cmp99Eq360C6dSourceSeparatedAmbientGreen
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall‖ ≤
      (cmp99Eq360C6dSourceBaselinePhysicalCoercivity
        (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
        (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
        (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1)
        (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
          (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
        (OmegaPrime0 := OmegaPrime0)
        R C hscale regions D hL halpha1 baselineRadiusBudget)⁻¹ := by
  unfold cmp99Eq360C6dSourceSeparatedAmbientGreen
    cmp99SourceAmbientDirichletGreen
  exact norm_covarianceOfIsCoerciveCLM_le _
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall) _

/-- The C6d canonical Green pulled back through the restricted form of the
same source-to-C6d carrier equivalence. -/
noncomputable def cmp99Eq360C6dSourceSeparatedPulledBackC6dGreen
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) :=
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
  finitePiLpTypedKernelReindex E.symm E.symm
    (cmp99Eq360C6dSourceAmbientBaselineDirichletGreen
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget hdepth hsmall)

/-- The internally generated source Green is exactly the pulled-back C6d
Green.  Both sides are constructed first; equality follows from the named
compression dictionary and uniqueness under the transported coercivity
floor. -/
theorem cmp99Eq360C6dSourceSeparatedAmbientGreen_eq_pullback
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    cmp99Eq360C6dSourceSeparatedAmbientGreen
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall =
    cmp99Eq360C6dSourceSeparatedPulledBackC6dGreen
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall := by
  let e := cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv
    (L := L) (K := K) (Q := Q) (depth := depth)
  let E := cmp99ActiveGaugeRegionSiteReindexEquiv e OmegaSource
  let Kc6d := cmp99Eq360C6dSourceSeparatedC6dAmbientPrecision
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
  let Ksource := finitePiLpTypedKernelReindex e.symm e.symm Kc6d
  let Ac6d := cmp99SourceAmbientDirichletPrecision
    (cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource) Kc6d
  let Asource := cmp99SourceAmbientDirichletPrecision OmegaSource Ksource
  let Gc6d := cmp99Eq360C6dSourceAmbientBaselineDirichletGreen
    (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
    (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
    (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1)
    (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
      (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
    (OmegaPrime0 := OmegaPrime0)
    R C hscale regions D hL halpha1 baselineRadiusBudget hdepth hsmall
  let Gsource := cmp99Eq360C6dSourceSeparatedAmbientGreen
    (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
    (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
    (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
    (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
    OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
    hdepth hsmall
  let Gpull := finitePiLpTypedKernelReindex E.symm E.symm Gc6d
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
  have hc : 0 < c := by
    exact cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
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
  have hKsource : IsCoerciveCLM Ksource c := by
    exact isCoerciveCLM_cmp99Eq360C6dSourceSeparatedAmbientPrecision
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
      hdepth hsmall
  have hAsource : IsCoerciveCLM Asource c := by
    exact isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
      OmegaSource Ksource hKsource
  have hsource : Asource.comp Gsource =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)) := by
    exact cmp99SourceAmbientDirichletPrecision_comp_green
      OmegaSource Ksource hc hKsource
  have hc6d : Ac6d.comp Gc6d =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99Eq360C6dSourceSeparatedAmbientRegion
            (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
          (SUNLieCoord Nc)) := by
    exact cmp99Eq360C6dSourceAmbientBaselinePrecision_comp_dirichletGreen
      (L := L ^ (depth + 1)) (N' := 2 * (K * Q)) (M := L)
      (Mlarge := Mlarge) (Nc := Nc) (n := n) (depth := depth)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1)
      (Omega := cmp99Eq360C6dSourceSeparatedAmbientRegion
        (L := L) (K := K) (Q := Q) (depth := depth) OmegaSource)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hL halpha1 baselineRadiusBudget hdepth hsmall
  have hpullTransport :
      (finitePiLpTypedKernelReindex E.symm E.symm Ac6d).comp Gpull =
        ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)) := by
    exact finitePiLpTypedKernelReindex_comp_eq_id E.symm Ac6d Gc6d hc6d
  have hAeq : Asource =
      finitePiLpTypedKernelReindex E.symm E.symm Ac6d := by
    exact cmp99Eq360C6dSourceSeparatedDirichletPrecision_eq_pullback
      (L := L) (K := K) (Q := Q) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (OmegaPrime0 := OmegaPrime0)
      OmegaSource R C hscale regions D hL halpha1 baselineRadiusBudget
  have hpull : Asource.comp Gpull =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc)) := by
    rw [hAeq]
    exact hpullTransport
  change Gsource = Gpull
  apply ContinuousLinearMap.ext
  intro phi
  apply isCoerciveCLM_injective Asource hc hAsource
  have hs := congrArg
    (fun T : ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) => T phi)
    hsource
  have hp := congrArg
    (fun T : ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc) => T phi)
    hpull
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using hs.trans hp.symm

end

end YangMills.RG
