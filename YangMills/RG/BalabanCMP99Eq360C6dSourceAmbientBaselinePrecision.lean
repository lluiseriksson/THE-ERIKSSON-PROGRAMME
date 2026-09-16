import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision
import YangMills.RG.BalabanCMP99Eq360C6dSourceBaselineGreen


namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

variable {L N' M Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero N'] [NeZero M] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
variable {U : PhysicalGaugeBackground 4 (L * N') Nc}
variable {eta alpha0 alpha1 : ℝ}
variable (R : CMP99Eq335PhysicalRegularityClass
  (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
  (scaleExtent := scaleExtent) (S := S)
  (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
variable (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge
  scaleExtent S scaleExtent_pos)
variable (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
variable {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
variable (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
variable (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
variable (hM : 2 ≤ M) (halpha1 : alpha1 ≤ 1 / 2)
variable (baselineRadiusBudget : CMP99SourceUbarClosedBudget 4 M Nc depth
  (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))

/-- The one full-carrier precision whose Dirichlet compression is intended to
be the literal C6d baseline precision. -/
noncomputable def cmp99Eq360C6dSourceAmbientBaselinePrecision :
    PhysicalGaugeZeroCochain 4 (L * N') Nc →L[ℝ]
      PhysicalGaugeZeroCochain 4 (L * N') Nc :=
  cmp99SourceActiveRegionFullCompanionAmbientPrecision regions
    (by norm_num : 2 ≤ 4) hM (matrixSUNAdjointModel Nc) eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    (cmp99Eq360C6dSourceLaplacianRetainedExtension
      (R := R) (C := C) (hscale := hscale) regions)
    baselineRadiusBudget.toRadiusChain
    (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
      (R := R) (C := C) (hscale := hscale) (regions := regions)
      (D := D) (halpha1 := halpha1)
      (baselineRadiusBudget := baselineRadiusBudget))

/-- Its literal Dirichlet compression is the already defined C6d baseline
precision, with no ambient or regional operator accepted from the caller. -/
theorem cmp99RegionalDirichletPrecision_C6dSourceAmbientBaseline_eq :
    let W := R.toCubeWitness C alpha1 hscale
    let T0 := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
      R C hscale regions D hM halpha1 baselineRadiusBudget
    let b := cmp99Eq360C6dSourcePhysicalCountingCoefficient
      R C hscale regions D hM halpha1 baselineRadiusBudget
    cmp99SourceAmbientDirichletPrecision
        (d := 4) (N := L * N') (g := SUNLieCoord Nc) Omega
        (cmp99Eq360C6dSourceAmbientBaselinePrecision
          (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
          (OmegaPrime0 := OmegaPrime0)
          R C hscale regions D hM halpha1 baselineRadiusBudget) =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) W.transformedBackground eta)
        T0.Qprime b := by
  dsimp only
  rw [cmp99Eq360C6dSourceBaselinePrecision_eq_laplacianRetainedPrecision
    R C hscale regions D hM halpha1 baselineRadiusBudget]
  rw [cmp99Eq360C6dSourcePhysicalCountingCoefficient_eq_laplacianRetained
    R C hscale regions D hM halpha1 baselineRadiusBudget]
  exact cmp99SourceAmbientDirichletPrecision_fullCompanion_eq regions
    (by norm_num : 2 ≤ 4) hM (matrixSUNAdjointModel Nc) eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    (cmp99Eq360C6dSourceLaplacianRetainedExtension
      (R := R) (C := C) (hscale := hscale) regions)
    baselineRadiusBudget.toRadiusChain
    (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
      (R := R) (C := C) (hscale := hscale) (regions := regions)
      (D := D) (halpha1 := halpha1)
      (baselineRadiusBudget := baselineRadiusBudget))

/-- The full-companion coercivity floor is literally the C6d baseline floor.
The only non-definitional ingredient is the already named equality between
the full and regional source-flow counting coefficients. -/
theorem cmp99SourceActiveRegionFullCompanionPhysicalCoercivity_eq_C6dBaseline :
    let Tfull := cmp99SourceActiveRegionFullCompanionTower regions
      (by norm_num : 2 ≤ 4) hM (matrixSUNAdjointModel Nc) eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      (cmp99Eq360C6dSourceLaplacianRetainedExtension
        (R := R) (C := C) (hscale := hscale) regions)
      baselineRadiusBudget.toRadiusChain
      (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
        (R := R) (C := C) (hscale := hscale) (regions := regions)
        (D := D) (halpha1 := halpha1)
        (baselineRadiusBudget := baselineRadiusBudget))
    cmp99SourceActiveRegionTerminalPhysicalCoercivity Tfull M depth
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) =
      cmp99Eq360C6dSourceBaselinePhysicalCoercivity
        R C hscale regions D hM halpha1 baselineRadiusBudget := by
  dsimp only
  unfold cmp99Eq360C6dSourceBaselinePhysicalCoercivity
  unfold cmp99SourceActiveRegionTerminalPhysicalCoercivity
  have hcoeff := cmp99SourceActiveRegionFullCompanionCountingCoefficient_eq_regional
    (d := 4) (M := M) (N := L * N') (Nc := Nc) (Omega := Omega)
    (depth := depth) regions (by norm_num : 2 ≤ 4) hM
    (matrixSUNAdjointModel Nc) eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    (cmp99Eq360C6dSourceLaplacianRetainedExtension
      (R := R) (C := C) (hscale := hscale) regions)
    baselineRadiusBudget.toRadiusChain
    (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
      (R := R) (C := C) (hscale := hscale) (regions := regions)
      (D := D) (halpha1 := halpha1)
      (baselineRadiusBudget := baselineRadiusBudget))
  exact congrArg
    (cmp99SourceActiveRegionTerminalCoercivity 4 M depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1))
    (by
      simpa only [cmp99SourceActiveRegionFullCompanionCountingCoefficient,
        cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower] using hcoeff)

/-- Positive-depth coercivity of the same ambient precision. -/
theorem isCoerciveCLM_cmp99Eq360C6dSourceAmbientBaselinePrecision
    (hdepth : 0 < depth) (heta : 0 < eta)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    let Tfull := cmp99SourceActiveRegionFullCompanionTower regions
      (by norm_num : 2 ≤ 4) hM (matrixSUNAdjointModel Nc) eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      (cmp99Eq360C6dSourceLaplacianRetainedExtension
        (R := R) (C := C) (hscale := hscale) regions)
      baselineRadiusBudget.toRadiusChain
      (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
        (R := R) (C := C) (hscale := hscale) (regions := regions)
        (D := D) (halpha1 := halpha1)
        (baselineRadiusBudget := baselineRadiusBudget))
    IsCoerciveCLM
      (cmp99Eq360C6dSourceAmbientBaselinePrecision R C hscale regions D hM
        halpha1 baselineRadiusBudget)
      (cmp99Eq360C6dSourceBaselinePhysicalCoercivity
        R C hscale regions D hM halpha1 baselineRadiusBudget) := by
  rw [← cmp99SourceActiveRegionFullCompanionPhysicalCoercivity_eq_C6dBaseline
    R C hscale regions D hM halpha1 baselineRadiusBudget]
  exact isCoerciveCLM_cmp99SourceActiveRegionFullCompanionAmbientPrecision
    (d := 4) (M := M) (N := L * N') (Nc := Nc) (Omega := Omega)
    (depth := depth) (spacing := eta)
    (epsilon := cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    regions (by norm_num : 2 ≤ 4) hM hdepth heta
    (cmp99Eq360C6dSourceLaplacianRetainedExtension
      (R := R) (C := C) (hscale := hscale) regions)
    baselineRadiusBudget.toRadiusChain
    (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
      (R := R) (C := C) (hscale := hscale) (regions := regions)
      (D := D) (halpha1 := halpha1)
      (baselineRadiusBudget := baselineRadiusBudget)) hsmall

/-- The generic Dirichlet compression of the source ambient precision is
coercive with the same literal C6d baseline floor. -/
theorem isCoerciveCLM_cmp99Eq360C6dSourceAmbientBaselineCompression
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    IsCoerciveCLM
      (cmp99SourceAmbientDirichletPrecision
        (d := 4) (N := L * N') (g := SUNLieCoord Nc) Omega
        (cmp99Eq360C6dSourceAmbientBaselinePrecision
          (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
          (OmegaPrime0 := OmegaPrime0)
          R C hscale regions D hM halpha1 baselineRadiusBudget))
      (cmp99Eq360C6dSourceBaselinePhysicalCoercivity
        R C hscale regions D hM halpha1 baselineRadiusBudget) := by
  exact isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
    (d := 4) (N := L * N') (g := SUNLieCoord Nc) Omega
    (cmp99Eq360C6dSourceAmbientBaselinePrecision
      (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hM halpha1 baselineRadiusBudget)
    (isCoerciveCLM_cmp99Eq360C6dSourceAmbientBaselinePrecision
      (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)

/-- The canonical Green of the literal ambient precision after Dirichlet
compression.  No regional inverse or operator equality is caller data. -/
noncomputable def cmp99Eq360C6dSourceAmbientBaselineDirichletGreen
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  covarianceOfIsCoerciveCLM
    (cmp99SourceAmbientDirichletPrecision Omega
      (cmp99Eq360C6dSourceAmbientBaselinePrecision
        R C hscale regions D hM halpha1 baselineRadiusBudget))
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)
    (isCoerciveCLM_cmp99Eq360C6dSourceAmbientBaselineCompression
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)

/-- The literal compressed ambient precision is a left inverse of its
internally constructed Green. -/
theorem cmp99Eq360C6dSourceAmbientBaselinePrecision_comp_dirichletGreen
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    (cmp99SourceAmbientDirichletPrecision
      (d := 4) (N := L * N') (g := SUNLieCoord Nc) Omega
      (cmp99Eq360C6dSourceAmbientBaselinePrecision
        (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
        (OmegaPrime0 := OmegaPrime0)
        R C hscale regions D hM halpha1 baselineRadiusBudget)).comp
        (cmp99Eq360C6dSourceAmbientBaselineDirichletGreen
          (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
          (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
          (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
          (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
          (OmegaPrime0 := OmegaPrime0)
          R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall) _

private theorem rightInverse_unique_of_operator_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A₁ A₂ G₁ G₂ : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA₂ : IsCoerciveCLM A₂ c) (hA : A₁ = A₂)
    (h₁ : A₁.comp G₁ = ContinuousLinearMap.id ℝ E)
    (h₂ : A₂.comp G₂ = ContinuousLinearMap.id ℝ E) :
    G₁ = G₂ := by
  apply ContinuousLinearMap.ext
  intro x
  apply isCoerciveCLM_injective A₂ hc hA₂
  have h₁x := congrArg (fun T : E →L[ℝ] E => T x) h₁
  have h₂x := congrArg (fun T : E →L[ℝ] E => T x) h₂
  rw [hA] at h₁x
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using h₁x.trans h₂x.symm

/-- Uniqueness of the inverse identifies the ambiently generated Dirichlet
Green with the already constructed literal C6d baseline Green. -/
theorem cmp99Eq360C6dSourceAmbientBaselineDirichletGreen_eq_baseline
    (hdepth : 0 < depth)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M depth eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    cmp99Eq360C6dSourceAmbientBaselineDirichletGreen
      (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
      (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
      (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
      (OmegaPrime0 := OmegaPrime0)
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall =
      cmp99Eq360C6dSourceBaselinePhysicalGreen
        (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
        (OmegaPrime0 := OmegaPrime0)
        R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall := by
  exact rightInverse_unique_of_operator_eq
    (cmp99SourceAmbientDirichletPrecision
      (d := 4) (N := L * N') (g := SUNLieCoord Nc) Omega
      (cmp99Eq360C6dSourceAmbientBaselinePrecision
        (L := L) (N' := N') (M := M) (Mlarge := Mlarge) (Nc := Nc)
        (n := n) (depth := depth) (scaleExtent := scaleExtent) (S := S)
        (scaleExtent_pos := scaleExtent_pos) (U := U) (eta := eta)
        (alpha0 := alpha0) (alpha1 := alpha1) (Omega := Omega)
        (OmegaPrime0 := OmegaPrime0)
        R C hscale regions D hM halpha1 baselineRadiusBudget))
    (cmp99Eq360C6dSourceBaselinePhysicalPrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget)
    (cmp99Eq360C6dSourceAmbientBaselineDirichletGreen
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)
    (cmp99Eq360C6dSourceBaselinePhysicalGreen
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)
    (isCoerciveCLM_cmp99Eq360C6dSourceBaselinePhysicalPrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)
    (cmp99RegionalDirichletPrecision_C6dSourceAmbientBaseline_eq
      R C hscale regions D hM halpha1 baselineRadiusBudget)
    (cmp99Eq360C6dSourceAmbientBaselinePrecision_comp_dirichletGreen
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)
    (cmp99Eq360C6dSourceBaselinePhysicalPrecision_comp_green
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)

end

end YangMills.RG
