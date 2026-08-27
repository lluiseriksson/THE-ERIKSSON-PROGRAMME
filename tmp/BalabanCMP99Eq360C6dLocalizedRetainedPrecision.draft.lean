import tmp.BalabanCMP99SourcePhysicalRealSliceTowerPair.draft
import tmp.BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget.draft
import YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacian
import YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice
import YangMills.RG.BalabanCMP99Eq360ComplexLocalLaplacianPerturbation
import YangMills.RG.BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation
import tmp.BalabanCMP99Eq360WeightedPrecisionRealSlice.draft
import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexBaselineRealSlice
import YangMills.RG.BalabanCMP99SourceUbarRadiusBudget

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# C6d-specific complex precision identity for CMP99 (3.60)

The Laplacian and averaging backgrounds are deliberately different internal
objects.  The regional Laplacian consumes the full transformed background
and the full physical perturbing one-cochain.  The Eq. (3.59) pair consumes
their canonical retained extensions.  Thus the source carrier distinction
sealed by C6d.1 is not erased by a single freely supplied background.

No tower, `F2`, starred partner, Laplacian, precision, or equality between
independently chosen operators is caller data.  This file proves only the
exact four-term identity.  The local estimates (3.61)--(3.63), inversion and
the four actions entering (3.42) remain separate downstream obligations.
-/

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

/-- The auxiliary closed-radius dimension is nonzero for the already printed
source gate `2 ≤ M`; it is not an additional caller hypothesis. -/
def cmp99Eq360C6dRadiusDimensionNeZero (hM : 2 ≤ M) :
    NeZero (4 * (M - 1)) :=
  ⟨by omega⟩

/-- Genuine scalar/source gates needed after C6d.1.  The physical background
is not a field: it is generated below from the regularity-class witness.
The complex perturbation is likewise generated from the physical `A`, with
the retained extension chosen internally for the averaging branch. -/
structure CMP99Eq360C6dLocalizedRetainedInput
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C)
    (hM : 2 ≤ M) (halpha1 : alpha1 ≤ 1 / 2)
    (baselineRadiusBudget : CMP99SourceUbarClosedBudget 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)) where
  A : PhysicalGaugeOneCochain 4 (L * N') Nc
  z rA Rmax : ℝ
  rA_nonneg : 0 ≤ rA
  retainedA_bound : ∀ b,
    ‖regions.retainedFineComplexOneCochain A b‖ ≤ rA
  perturbation_small : |z| *
    (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2
  radiusBudget :
    letI : NeZero (4 * (M - 1)) :=
      cmp99Eq360C6dRadiusDimensionNeZero hM
    CMP99ComplexClosedRadiusBudget (4 * (M - 1)) M depth
      (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) z rA)
      Rmax (cmp99UbarNoWindingThreshold Nc)
  a_j : ℝ

namespace CMP99Eq360C6dLocalizedRetainedInput

variable {U : PhysicalGaugeBackground 4 (L * N') Nc}
variable {eta alpha0 alpha1 : ℝ}
variable {R : CMP99Eq335PhysicalRegularityClass
  (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
  (scaleExtent := scaleExtent) (S := S)
  (scaleExtent_pos := scaleExtent_pos) U eta alpha0}
variable {C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
  scaleExtent_pos}
variable {hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1}
variable {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
variable {regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth}
variable {D : CMP99Eq335Corollary36SourceRegionDictionary Omega OmegaPrime0 C}
variable {hM : 2 ≤ M} {halpha1 : alpha1 ≤ 1 / 2}
variable {baselineRadiusBudget : CMP99SourceUbarClosedBudget 4 M Nc depth
  (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)}

/-- The baseline recursive proof object is generated from one closed scalar
budget.  No per-scale radius family is accepted by the C6d input. -/
noncomputable def baselineRadiusChain
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) :=
  baselineRadiusBudget.toRadiusChain

/-- The full analytic perturbation used only by the Laplacian branch. -/
noncomputable def fullComplexOneCochain
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    CMP99Eq337PhysicalComplexOneCochain 4 (L * N') Nc :=
  cmp99Eq337PhysicalComplexifyOneCochain I.A

/-- Full baseline background for the regional Laplacian. -/
noncomputable def fullBackground0
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    GaugeConfig 4 (L * N') (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
  let W := R.toCubeWitness C alpha1 hscale
  cmp99Eq337PhysicalComplexPerturbedBackground W.transformedBackground
    I.fullComplexOneCochain 0

/-- Full perturbed background for the regional Laplacian. -/
noncomputable def fullBackground1
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    GaugeConfig 4 (L * N') (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
  let W := R.toCubeWitness C alpha1 hscale
  cmp99Eq337PhysicalComplexPerturbedBackground W.transformedBackground
    I.fullComplexOneCochain I.z

/-- The full baseline is the canonical compact-real-slice embedding.  This
named equality prevents the zero branch from becoming a second background
choice. -/
theorem fullBackground0_eq_realSlice
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.fullBackground0 =
      cmp99PhysicalGaugeBackgroundToSpecialLinear
        (R.toCubeWitness C alpha1 hscale).transformedBackground := by
  exact cmp99Eq337PhysicalComplexPerturbedBackground_zero_realSlice
    (R.toCubeWitness C alpha1 hscale).transformedBackground I.A

/-- At a real perturbation parameter the full analytic branch is exactly the
canonical complex image of the physical left variation. -/
theorem fullBackground1_eq_realSlice
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.fullBackground1 =
      cmp99PhysicalGaugeBackgroundToSpecialLinear
        (cmp98PhysicalSuLeftVariation
          (R.toCubeWitness C alpha1 hscale).transformedBackground I.A I.z) := by
  exact cmp99Eq337PhysicalComplexPerturbedBackground_realSlice
    (R.toCubeWitness C alpha1 hscale).transformedBackground I.A I.z

/-- Canonical compact-real-slice agreement for the baseline retained tower.
The physical tower and the analytic tower are both built internally, at the
literal matrix `SUN` adjoint model. -/
noncomputable def baselineRetainedTowerRealSliceAgreement
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) : by
    let W := R.toCubeWitness C alpha1 hscale
    let retainedU := regions.retainedFineExtension W.transformedBackground
    let hlocal := W.retainedFineReadBonds_nearIdentity regions
      (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
        C D regions)
      halpha1
    let retainedUSmall := regions.norm_retainedFineExtension_sub_one_le
      W.transformedBackground
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      I.baselineRadiusChain.epsilon_nonneg hlocal
    exact CMP99Eq359TowerRealSliceAgreement
      (regions.physicalRealSliceComplexTower (by norm_num : 2 ≤ 4) hM eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
        retainedU I.baselineRadiusChain retainedUSmall).toComplexTower
      (regions.weightedQprimeTower (by norm_num : 2 ≤ 4) hM
        (matrixSUNAdjointModel Nc) eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
        retainedU I.baselineRadiusChain retainedUSmall) := by
  let W := R.toCubeWitness C alpha1 hscale
  let retainedU := regions.retainedFineExtension W.transformedBackground
  let hlocal := W.retainedFineReadBonds_nearIdentity regions
    (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
      C D regions)
    halpha1
  let retainedUSmall := regions.norm_retainedFineExtension_sub_one_le
    W.transformedBackground
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    I.baselineRadiusChain.epsilon_nonneg hlocal
  exact regions.physicalRealSliceTowerAgreement
    (by norm_num : 2 ≤ 4) hM eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    retainedU I.baselineRadiusChain retainedUSmall

/-- Physical weighted tower underlying the C6d.1 counting-Hilbert precision.
It is regenerated from the same retained background and radius chain used by
the analytic baseline; no terminal operator is supplied by the caller. -/
noncomputable def baselineRetainedPhysicalTower
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega eta := by
  let W := R.toCubeWitness C alpha1 hscale
  let retainedU := regions.retainedFineExtension W.transformedBackground
  let hlocal := W.retainedFineReadBonds_nearIdentity regions
    (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
      C D regions)
    halpha1
  let retainedUSmall := regions.norm_retainedFineExtension_sub_one_le
    W.transformedBackground
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    I.baselineRadiusChain.epsilon_nonneg hlocal
  exact regions.weightedQprimeTower (by norm_num : 2 ≤ 4) hM
    (matrixSUNAdjointModel Nc) eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    retainedU I.baselineRadiusChain retainedUSmall

/-- Analytic compact-real-slice tower generated from the same retained
baseline data as `baselineRetainedPhysicalTower`. -/
noncomputable def baselineRetainedComplexTower
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    CMP99ComplexRegionalTower (Nc := Nc) Omega eta := by
  let W := R.toCubeWitness C alpha1 hscale
  let retainedU := regions.retainedFineExtension W.transformedBackground
  let hlocal := W.retainedFineReadBonds_nearIdentity regions
    (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
      C D regions)
    halpha1
  let retainedUSmall := regions.norm_retainedFineExtension_sub_one_le
    W.transformedBackground
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    I.baselineRadiusChain.epsilon_nonneg hlocal
  exact (regions.physicalRealSliceComplexTower (by norm_num : 2 ≤ 4) hM eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    retainedU I.baselineRadiusChain retainedUSmall).toComplexTower

/-- Named compact real-slice agreement between the two internally generated
baseline towers. -/
noncomputable def baselineRetainedNamedRealSliceAgreement
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    CMP99Eq359TowerRealSliceAgreement I.baselineRetainedComplexTower
      I.baselineRetainedPhysicalTower := by
  simpa [baselineRetainedComplexTower, baselineRetainedPhysicalTower] using
    I.baselineRetainedTowerRealSliceAgreement

/-- Printed weighted-adjoint coefficient induced by the literal C6d.1
counting coefficient.  The terminal volume ratio is computed from the
internally generated tower rather than accepted as a scalar dictionary. -/
noncomputable def weightedPrecisionCoefficient
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) : ℝ :=
  cmp99SourceCountingCoefficientAsWeightedAdjoint
    I.baselineRetainedPhysicalTower I.a_j

/-- Literal real C6d.1 precision whose counting coefficient is `a_j`.
Naming this object prevents the compact real slice from targeting a freshly
chosen real precision with the same type. -/
noncomputable def baselinePhysicalPrecision
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  R.localizedRetainedPhysicalPrecision C hscale regions D hM
    (matrixSUNAdjointModel Nc) halpha1 I.baselineRadiusChain I.a_j

/-- The source regularity spacing is positive, hence the terminal spacing of
the internally generated physical tower is nonzero.  Eq. (3.60) does not need
another caller-supplied denominator gate. -/
theorem baselineRetainedPhysicalTower_terminalSpacing_ne_zero
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.baselineRetainedPhysicalTower.terminalSpacing ≠ 0 := by
  unfold baselineRetainedPhysicalTower
  rw [regions.weightedQprimeTower_terminalSpacing]
  have hM0 : (M : ℝ) ≠ 0 := by
    exact_mod_cast (show M ≠ 0 by omega)
  exact mul_ne_zero (pow_ne_zero depth hM0) R.eta_pos.ne'

/-- C6d.1's literal localized counting precision is the source precision on
the named generated baseline tower.  The equality is obtained from the
sealed localized/canonical terminal dictionary, not from a caller-supplied
operator equality. -/
theorem baselinePhysicalPrecision_eq_generated
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    let W := R.toCubeWitness C alpha1 hscale
    I.baselinePhysicalPrecision =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) W.transformedBackground eta)
        I.baselineRetainedPhysicalTower.Qprime I.a_j := by
  let W := R.toCubeWitness C alpha1 hscale
  let T := R.localizedRetainedTowerOfSourceRegion
    (spacing := eta) C hscale regions D hM (matrixSUNAdjointModel Nc)
      halpha1 I.baselineRadiusChain
  change R.localizedRetainedPhysicalPrecision C hscale regions D hM
      (matrixSUNAdjointModel Nc) halpha1 I.baselineRadiusChain I.a_j = _
  calc
    _ = cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) W.transformedBackground eta)
        (T.canonicalTowerAt (Fin.last depth)).Qprime I.a_j :=
      R.localizedRetainedPhysicalPrecision_eq_canonical C hscale regions D
        hM (matrixSUNAdjointModel Nc) halpha1 I.baselineRadiusChain I.a_j
    _ = _ := by
      rw [T.canonicalTerminal_eq_generated]
      rfl

/-- The Eq. (3.59) pair uses only the canonical retained physical extensions.
The perturbed physical radius chain is derived from the stronger closed
complex budget; it is not a second caller hypothesis.  Both analytic branches
are then generated as literal compact real slices on the common terminal
bundle determined internally by `regions`. -/
noncomputable def retainedTowerPair
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega eta := by
  let W := R.toCubeWitness C alpha1 hscale
  let epsilon0 := cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1
  let epsilon1 := cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc
    epsilon0 I.z I.rA
  let retainedU := regions.retainedFineExtension W.transformedBackground
  let retainedA := regions.retainedFineOneCochainExtension I.A
  let perturbedU := cmp98PhysicalSuLeftVariation retainedU retainedA I.z
  have hlocal : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(W.transformedBackground (positiveEdgeOfPhysicalBond q) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          epsilon0 :=
    W.retainedFineReadBonds_nearIdentity regions
      (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
        C D regions)
      halpha1
  have retainedU_small : ∀ e : ConcreteEdge 4 (L * N'),
      ‖(retainedU e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon0 :=
    regions.norm_retainedFineExtension_sub_one_le
      W.transformedBackground epsilon0
        I.baselineRadiusChain.epsilon_nonneg hlocal
  have retainedU_positive_small : ∀ b,
      ‖(retainedU (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon0 := by
    intro b
    exact retainedU_small (positiveEdgeOfPhysicalBond b)
  have retainedA_bound : ∀ b,
      ‖cmp99Eq337PhysicalComplexifyOneCochain retainedA b‖ ≤ I.rA := by
    intro b
    simpa [retainedA,
      CMP99SourceActiveRegionChain.retainedFineComplexOneCochain] using
      I.retainedA_bound b
  have analyticPerturbedSmall : ∀ b,
      ‖(cmp99Eq337PhysicalComplexPerturbedBackground retainedU
          (cmp99Eq337PhysicalComplexifyOneCochain retainedA) I.z b :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon1 := by
    intro b
    simpa [epsilon1] using
      norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
        retainedU (cmp99Eq337PhysicalComplexifyOneCochain retainedA) I.z
        epsilon0 I.rA retainedA_bound I.perturbation_small
        retainedU_positive_small b
  have perturbedU_small : ∀ e : ConcreteEdge 4 (L * N'),
      ‖(perturbedU e :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon1 := by
    have hslice := cmp99Eq337PhysicalComplexPerturbedBackground_realSlice
      retainedU retainedA I.z
    rw [hslice] at analyticPerturbedSmall
    intro e
    simpa [perturbedU] using analyticPerturbedSmall e
  let chain1 : CMP99SourceUbarRadiusChain 4 M Nc depth epsilon1 :=
    I.radiusBudget.toSourceUbarRadiusChain (by norm_num : 2 ≤ 4) hM
  exact regions.physicalRealSliceComplexTowerPair
    (by norm_num : 2 ≤ 4) hM eta epsilon0 epsilon1 retainedU perturbedU
    I.baselineRadiusChain chain1 retainedU_small perturbedU_small

/-- The baseline forward field of the Eq. (3.59) pair is the separately
named baseline compact-real-slice tower, not another chosen operator. -/
theorem retainedTowerPair_Q0_eq_baselineRetainedComplexTower
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.retainedTowerPair.Q0 = I.baselineRetainedComplexTower.Qprime := by
  rfl

/-- The baseline printed-starred field of the pair is the independently
generated starred synthesis of the named baseline tower. -/
theorem retainedTowerPair_starred0_eq_baselineRetainedComplexTower
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.retainedTowerPair.starred0 = I.baselineRetainedComplexTower.starred := by
  rfl

/-- Literal full-background baseline regional Laplacian. -/
noncomputable def baselineLaplacian
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalLaplacian Omega I.fullBackground0 eta

/-- Literal full-background perturbed regional Laplacian. -/
noncomputable def perturbedLaplacian
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalLaplacian Omega I.fullBackground1 eta

/-- The named analytic baseline Laplacian is exactly the compact real slice
of the literal C6d.1 physical Laplacian. -/
theorem baselineLaplacian_realSlice
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    I.baselineLaplacian
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc)
          (R.toCubeWitness C alpha1 hscale).transformedBackground eta phi) := by
  ext x
  rw [baselineLaplacian, I.fullBackground0_eq_realSlice]
  exact cmp99Eq360ComplexRegionalLaplacian_realSlice Omega
    (R.toCubeWitness C alpha1 hscale).transformedBackground eta phi x

/-- The full-carrier local three-species term `V'_1(A)` is constructed from
the two analytic stencils, not accepted as their difference. -/
noncomputable def localLaplacianPerturbation
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexLocalLaplacianPerturbation Omega
    I.fullBackground0 I.fullBackground1 eta

/-- Complete baseline analytic precision with the internally built retained
average and independently built printed-starred synthesis. -/
noncomputable def baselinePrecision
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalPrecision I.baselineLaplacian
    I.retainedTowerPair.Q0 I.retainedTowerPair.starred0
      (I.weightedPrecisionCoefficient : ℂ)

/-- The analytic baseline precision at the internally derived weighted
coefficient is exactly the compact real slice of the literal C6d.1 counting
precision.  This is the normalization-sensitive bridge needed before any
regional inverse may be identified. -/
theorem baselinePrecision_realSlice
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    I.baselinePrecision
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (I.baselinePhysicalPrecision phi) := by
  rw [baselinePrecision,
    I.retainedTowerPair_Q0_eq_baselineRetainedComplexTower,
    I.retainedTowerPair_starred0_eq_baselineRetainedComplexTower,
    I.baselinePhysicalPrecision_eq_generated]
  exact cmp99Eq360ComplexRegionalPrecision_realSlice_weighted
    I.baselineRetainedComplexTower I.baselineRetainedPhysicalTower
    I.baselineRetainedNamedRealSliceAgreement I.baselineLaplacian
    (cmp99ActiveRegionSourceCovariantLaplacian Omega
      (matrixSUNAdjointModel Nc)
      (R.toCubeWitness C alpha1 hscale).transformedBackground eta)
    I.baselineLaplacian_realSlice I.a_j
    I.baselineRetainedPhysicalTower_terminalSpacing_ne_zero phi

/-- Complete perturbed analytic precision on the same regional carrier. -/
noncomputable def perturbedPrecision
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalPrecision I.perturbedLaplacian
    I.retainedTowerPair.Q1 I.retainedTowerPair.starred1
      (I.weightedPrecisionCoefficient : ℂ)

/-- Literal four-term perturbation with no merged norm budget. -/
noncomputable def precisionPerturbation
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99Eq360ComplexRegionalPrecisionPerturbation I.retainedTowerPair
    I.baselineLaplacian I.perturbedLaplacian
      (I.weightedPrecisionCoefficient : ℂ)

/-- Source-expanded perturbation: the local `V'_1(A)` and the three
averaging terms remain four separately inspectable summands. -/
noncomputable def sourcePrecisionPerturbation
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  I.localLaplacianPerturbation -
    (I.weightedPrecisionCoefficient : ℂ) •
      (I.retainedTowerPair.F2star.comp I.retainedTowerPair.Q0) -
    (I.weightedPrecisionCoefficient : ℂ) •
      (I.retainedTowerPair.starred0.comp I.retainedTowerPair.F2) -
    (I.weightedPrecisionCoefficient : ℂ) •
      (I.retainedTowerPair.F2star.comp I.retainedTowerPair.F2)

/-- The literal stencil identity replaces the unexpanded Laplacian
difference without changing any averaging term. -/
theorem precisionPerturbation_eq_sourcePrecisionPerturbation
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.precisionPerturbation = I.sourcePrecisionPerturbation := by
  unfold precisionPerturbation sourcePrecisionPerturbation
  rw [cmp99Eq360_complexRegionalLaplacian_sub_eq_localPerturbation]
  rfl

/-- Exact C6d specialization of CMP99 (3.60).  The equality is derived from
the internally constructed operators; none of its two sides is input. -/
theorem perturbedPrecision_eq_baselinePrecision_sub_perturbation
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.perturbedPrecision =
      I.baselinePrecision - I.precisionPerturbation := by
  exact cmp99Eq360_complexRegionalPrecision_eq_sub_perturbation
    I.retainedTowerPair I.baselineLaplacian I.perturbedLaplacian
      (I.weightedPrecisionCoefficient : ℂ)

/-- Source-expanded C6d Eq. (3.60), still before any norm estimate or
regional inverse is introduced. -/
theorem perturbedPrecision_eq_baselinePrecision_sub_sourcePerturbation
    (I : CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM
      halpha1 baselineRadiusBudget) :
    I.perturbedPrecision =
      I.baselinePrecision - I.sourcePrecisionPerturbation := by
  rw [← I.precisionPerturbation_eq_sourcePrecisionPerturbation]
  exact I.perturbedPrecision_eq_baselinePrecision_sub_perturbation

end CMP99Eq360C6dLocalizedRetainedInput

end

end YangMills.RG
