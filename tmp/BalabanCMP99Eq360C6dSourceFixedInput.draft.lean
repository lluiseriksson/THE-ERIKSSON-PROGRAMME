import tmp.BalabanCMP99Eq360C6dLocalizedRetainedPrecision.draft
import tmp.BalabanCMP99SourceActiveRegionTerminalCoercivity.draft
import tmp.BalabanCMP99Eq360C6dLaplacianRetainedExtension.draft
import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Source-fixed C6d input and its exact counting/weighted coefficient

The algebraic C6d input deliberately exposes the coefficient multiplying
Lean's counting-Hilbert `Qprime.adjoint * Qprime`.  CMP99 instead prints the
weighted coefficient `a_j * terminalSpacing^(-2)`.  This module constructs
the counting coefficient internally from the literal source recurrence and
the generated retained tower.  No caller-supplied coefficient or equality
between the two conventions is accepted.
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

/-- The generated physical retained tower, factored before an algebraic C6d
input is assembled.  In particular it cannot depend on the coefficient that
will later multiply its terminal averaging operator. -/
noncomputable def cmp99Eq360C6dSourceBaselineRetainedPhysicalTower :
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega eta := by
  let W := R.toCubeWitness C alpha1 hscale
  let retainedU := regions.retainedFineExtension W.transformedBackground
  let chain := baselineRadiusBudget.toRadiusChain
  let hlocal := W.retainedFineReadBonds_nearIdentity regions
    (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
      C D regions)
    halpha1
  let retainedUSmall := regions.norm_retainedFineExtension_sub_one_le
    W.transformedBackground
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    chain.epsilon_nonneg hlocal
  exact regions.weightedQprimeTower (by norm_num : 2 ≤ 4) hM
    (matrixSUNAdjointModel Nc) eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    retainedU chain retainedUSmall

/-- Literal source-fixed coefficient for Lean's counting-Hilbert adjoint.
Multiplying it by the exact counting-to-weighted ratio recovers the printed
`a_j * terminalSpacing^(-2)` coefficient. -/
noncomputable def cmp99Eq360C6dSourcePhysicalCountingCoefficient : ℝ :=
  let T := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
    R C hscale regions D hM halpha1 baselineRadiusBudget
  cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
    (cmp99SourceMassParameter 1 (M : ℝ) depth)

include D halpha1

/-- The same source regularity witness that controls the retained `Qprime`
carrier also controls every internal bond of the selected Laplacian region.
The proof uses only the printed region-in-cube dictionary and the existing
half-unit exponential window. -/
theorem cmp99Eq360C6dSource_internalBonds_nearIdentity :
    ∀ q ∈ Omega.bonds,
      ‖((R.toCubeWitness C alpha1 hscale).transformedBackground
          (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 := by
  intro q hq
  let W := R.toCubeWitness C alpha1 hscale
  have hendpoints :
      q.1 ∈ Omega.sites ∧ q.1.shift q.2 ∈ Omega.sites := by
    simpa [ActiveGaugeRegion.bonds] using hq
  have hD : CMP99Eq335Corollary36SourceRegionDictionary
      Omega OmegaPrime0 W.cube := by
    simpa [W, CMP99Eq335PhysicalRegularityClass.toCubeWitness] using D
  have hsource : q.1 ∈ W.cube.carrier := by
    apply hD.printed_omegaPrime0_subset_regularCube
    rw [← D.headRegion_eq_omegaPrime0]
    exact hendpoints.1
  let X : SuLie Nc :=
    (suLieCoordIso Nc).symm (W.logarithmicRepresentative q)
  have hX : ‖X.toMatrix‖ ≤
      cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 := by
    calc
      ‖X.toMatrix‖ ≤ ‖X‖ := norm_suLie_toMatrix_l2_opNorm_le X
      _ = ‖W.logarithmicRepresentative q‖ := by
        exact (suLieCoordIso Nc).symm.norm_map _
      _ ≤ cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 :=
        (W.amplitude_bound q.1 hsource q.2).le
  have hamplitude : |eta| *
      cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 ≤ alpha1 :=
    W.abs_eta_mul_amplitudeMajorant_le
  have hsmall : |eta| *
      cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 ≤ 1 / 2 :=
    hamplitude.trans halpha1
  have hexp := norm_exp_smul_sub_one_le_two_mul eta
    (cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0) X.toMatrix hX hsmall
  have hbackground :
      (W.transformedBackground (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
        physicalMatrixExp (eta • X.toMatrix) := by
    have hphysical :=
      W.transformedBackground_eq_exponential_on_internalBonds hD q hq
    exact congrArg (fun z : SUN Nc => (z : Matrix (Fin Nc) (Fin Nc) ℂ))
      hphysical
  rw [hbackground]
  calc
    ‖physicalMatrixExp (eta • X.toMatrix) - 1‖ ≤
        2 * (|eta| * cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0) := by
      simpa only [physicalMatrixExp] using hexp
    _ ≤ 2 * alpha1 := by gcongr
    _ = cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 := rfl

omit D halpha1

/-- Source-specialized union extension used only to prove the physical
coercivity estimate. -/
noncomputable def cmp99Eq360C6dSourceLaplacianRetainedExtension :
    PhysicalGaugeBackground 4 (L * N') Nc :=
  cmp99Eq360C6dLaplacianRetainedExtension regions
    (R.toCubeWitness C alpha1 hscale).transformedBackground

/-- The source gates generate global smallness of the union extension. -/
theorem norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le :
    ∀ e : ConcreteEdge 4 (L * N'),
      ‖(cmp99Eq360C6dSourceLaplacianRetainedExtension
          R C hscale regions D hM halpha1 baselineRadiusBudget e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 := by
  let W := R.toCubeWitness C alpha1 hscale
  let chain := baselineRadiusBudget.toRadiusChain
  let hretained := W.retainedFineReadBonds_nearIdentity regions
    (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
      C D regions)
    halpha1
  let hlaplacian := cmp99Eq360C6dSource_internalBonds_nearIdentity
    R C hscale regions D hM halpha1 baselineRadiusBudget
  exact norm_cmp99Eq360C6dLaplacianRetainedExtension_sub_one_le
    regions W.transformedBackground
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    chain.epsilon_nonneg hretained hlaplacian

/-- Physical retained tower generated from the union extension. -/
noncomputable def cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower :
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega eta :=
  regions.weightedQprimeTower (by norm_num : 2 ≤ 4) hM
    (matrixSUNAdjointModel Nc) eta
    (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
    (cmp99Eq360C6dSourceLaplacianRetainedExtension
      R C hscale regions D hM halpha1 baselineRadiusBudget)
    baselineRadiusBudget.toRadiusChain
    (norm_cmp99Eq360C6dSourceLaplacianRetainedExtension_sub_one_le
      R C hscale regions D hM halpha1 baselineRadiusBudget)

/-- Both retained constructions end in the same generated terminal Hilbert
bundle.  This equality is derived from the typed source-region chain; it is
not an identification supplied by the caller. -/
theorem cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower_terminalSpace_eq :
    (cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
      R C hscale regions D hM halpha1 baselineRadiusBudget).TerminalSpace =
    (cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower
      R C hscale regions D hM halpha1 baselineRadiusBudget).TerminalSpace := by
  unfold cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
  unfold cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower
  rw [regions.weightedQprimeTower_terminalSpace_eq,
    regions.weightedQprimeTower_terminalSpace_eq]

/-- Both technical extensions have the same generated terminal spacing. -/
theorem cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower_terminalSpacing :
    (cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower
      R C hscale regions D hM halpha1 baselineRadiusBudget).terminalSpacing =
      (M : ℝ) ^ depth * eta := by
  unfold cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower
  rw [regions.weightedQprimeTower_terminalSpacing]

/-- Consequently the source-fixed counting coefficient is identical whether
computed with the original retained extension or the Laplacian-aware one. -/
theorem cmp99Eq360C6dSourcePhysicalCountingCoefficient_eq_laplacianRetained :
    cmp99Eq360C6dSourcePhysicalCountingCoefficient
        R C hscale regions D hM halpha1 baselineRadiusBudget =
      cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
        (cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower
          R C hscale regions D hM halpha1 baselineRadiusBudget)
        (cmp99SourceMassParameter 1 (M : ℝ) depth) := by
  unfold cmp99Eq360C6dSourcePhysicalCountingCoefficient
  unfold cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
  rw [show
      (cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
        R C hscale regions D hM halpha1 baselineRadiusBudget).terminalSpacing =
          (M : ℝ) ^ depth * eta by
        unfold cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
        rw [regions.weightedQprimeTower_terminalSpacing],
    cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower_terminalSpacing]

/-- The source-generated retained tower and the Laplacian-aware global
extension have the same terminal `Qprime`.  Both operators are constructed
inside the theorem from the same source background and radius chain. -/
theorem cmp99Eq360C6dSourceBaselineRetainedPhysicalTower_Qprime_heq_laplacianExtension :
    let W := R.toCubeWitness C alpha1 hscale
    let chain := baselineRadiusBudget.toRadiusChain
    let hretained := W.retainedFineReadBonds_nearIdentity regions
      (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
        C D regions)
      halpha1
    let hlaplacian := cmp99Eq360C6dSource_internalBonds_nearIdentity
      R C hscale regions D hM halpha1 baselineRadiusBudget
    let V := cmp99Eq360C6dLaplacianRetainedExtension
      regions W.transformedBackground
    let hV := norm_cmp99Eq360C6dLaplacianRetainedExtension_sub_one_le
      regions W.transformedBackground
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      chain.epsilon_nonneg hretained hlaplacian
    HEq
      (cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
        R C hscale regions D hM halpha1 baselineRadiusBudget).Qprime
      (regions.weightedQprimeTower (by norm_num : 2 ≤ 4) hM
        (matrixSUNAdjointModel Nc) eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
        V chain hV).Qprime := by
  dsimp only
  let W := R.toCubeWitness C alpha1 hscale
  let chain := baselineRadiusBudget.toRadiusChain
  let hretained := W.retainedFineReadBonds_nearIdentity regions
    (CMP99Eq335Corollary36SourceRegionDictionary.retainedFineReadCarrierInsideRegularCube
      C D regions)
    halpha1
  let hlaplacian := cmp99Eq360C6dSource_internalBonds_nearIdentity
    R C hscale regions D hM halpha1 baselineRadiusBudget
  simpa only [cmp99Eq360C6dSourceBaselineRetainedPhysicalTower] using
    (cmp99Eq360C6d_retainedFineExtension_Qprime_heq_laplacianExtension
      regions (by norm_num : 2 ≤ 4) hM (matrixSUNAdjointModel Nc) eta
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      W.transformedBackground chain hretained hlaplacian)

/-- Exact equality between the literal C6d baseline precision and the
precision generated with the Laplacian-aware extension. -/
theorem cmp99Eq360C6dSourceBaselinePrecision_eq_laplacianRetainedPrecision :
    let W := R.toCubeWitness C alpha1 hscale
    let T0 := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
      R C hscale regions D hM halpha1 baselineRadiusBudget
    let T1 := cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower
      R C hscale regions D hM halpha1 baselineRadiusBudget
    let b := cmp99Eq360C6dSourcePhysicalCountingCoefficient
      R C hscale regions D hM halpha1 baselineRadiusBudget
    cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) W.transformedBackground eta)
        T0.Qprime b =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc)
          (cmp99Eq360C6dSourceLaplacianRetainedExtension
            R C hscale regions D hM halpha1 baselineRadiusBudget) eta)
        T1.Qprime b := by
  dsimp only
  apply cmp99SourceGaugePrecision_eq_of_laplacian_eq_of_Qprime_heq
  · exact
      cmp99ActiveRegionSourceCovariantLaplacian_eq_laplacianRetainedExtension
        regions (matrixSUNAdjointModel Nc)
        (R.toCubeWitness C alpha1 hscale).transformedBackground eta
  · exact cmp99Eq360C6dSourceLaplacianRetainedPhysicalTower_terminalSpace_eq
      R C hscale regions D hM halpha1 baselineRadiusBudget
  · exact
      cmp99Eq360C6dSourceBaselineRetainedPhysicalTower_Qprime_heq_laplacianExtension
        R C hscale regions D hM halpha1 baselineRadiusBudget

/-- Source-facing C6d input.  The perturbing field and its genuine radius
gates remain caller data, while the averaging coefficient is generated
internally from CMP99's recurrence and the retained tower. -/
noncomputable def cmp99Eq360C6dLocalizedRetainedSourceInput
    (A : PhysicalGaugeOneCochain 4 (L * N') Nc)
    (z rA Rmax : ℝ) (hrA : 0 ≤ rA)
    (hretained : ∀ b : PhysicalBond 4 (L * N'),
      ‖regions.retainedFineComplexOneCochain A b‖ ≤ rA)
    (hperturbation : |z| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (perturbationRadiusBudget :
      letI : NeZero (4 * (M - 1)) :=
        cmp99Eq360C6dRadiusDimensionNeZero hM
      CMP99ComplexClosedRadiusBudget (4 * (M - 1)) M depth
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc
          (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) z rA)
        Rmax (cmp99UbarNoWindingThreshold Nc)) :
    CMP99Eq360C6dLocalizedRetainedInput R C hscale regions D hM halpha1
      baselineRadiusBudget where
  A := A
  z := z
  rA := rA
  Rmax := Rmax
  rA_nonneg := hrA
  retainedA_bound := hretained
  perturbation_small := hperturbation
  radiusBudget := perturbationRadiusBudget
  a_j := cmp99Eq360C6dSourcePhysicalCountingCoefficient
    R C hscale regions D hM halpha1 baselineRadiusBudget

/-- The source constructor cannot silently replace the counting coefficient:
its value reduces to the unique coefficient generated above. -/
theorem cmp99Eq360C6dLocalizedRetainedSourceInput_a_j
    (A : PhysicalGaugeOneCochain 4 (L * N') Nc)
    (z rA Rmax : ℝ) (hrA : 0 ≤ rA)
    (hretained : ∀ b : PhysicalBond 4 (L * N'),
      ‖regions.retainedFineComplexOneCochain A b‖ ≤ rA)
    (hperturbation : |z| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (perturbationRadiusBudget :
      letI : NeZero (4 * (M - 1)) :=
        cmp99Eq360C6dRadiusDimensionNeZero hM
      CMP99ComplexClosedRadiusBudget (4 * (M - 1)) M depth
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc
          (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) z rA)
        Rmax (cmp99UbarNoWindingThreshold Nc)) :
    (cmp99Eq360C6dLocalizedRetainedSourceInput R C hscale regions D hM
      halpha1 baselineRadiusBudget A z rA Rmax hrA hretained hperturbation
      perturbationRadiusBudget).a_j =
      cmp99Eq360C6dSourcePhysicalCountingCoefficient
        R C hscale regions D hM halpha1 baselineRadiusBudget := by
  rfl

/-- The physical source coefficient is positive.  This is derived from the
source recurrence and generated terminal spacing, not accepted as data. -/
theorem cmp99Eq360C6dSourcePhysicalCountingCoefficient_pos
    (heta : 0 < eta) :
    0 < cmp99Eq360C6dSourcePhysicalCountingCoefficient
      R C hscale regions D hM halpha1 baselineRadiusBudget := by
  let T := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
    R C hscale regions D hM halpha1 baselineRadiusBudget
  have hMreal : (0 : ℝ) < M := by
    exact_mod_cast (NeZero.pos M)
  have haj : 0 < cmp99SourceMassParameter 1 (M : ℝ) depth :=
    cmp99SourceMassParameter_pos (by norm_num) hMreal depth
  have hterminal : 0 < T.terminalSpacing := by
    rw [show T.terminalSpacing = (M : ℝ) ^ depth * eta by
      unfold T cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
      rw [regions.weightedQprimeTower_terminalSpacing]]
    exact mul_pos (pow_pos hMreal depth) heta
  unfold cmp99Eq360C6dSourcePhysicalCountingCoefficient
  exact cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient_pos
    T haj heta hterminal

/-- The scalar convention gate: the internally generated counting
coefficient gives exactly the printed weighted coefficient. -/
theorem cmp99Eq360C6dSourcePhysicalCountingCoefficient_toWeighted
    (heta : eta ≠ 0) :
    let T := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
      R C hscale regions D hM halpha1 baselineRadiusBudget
    cmp99Eq360C6dSourcePhysicalCountingCoefficient
        R C hscale regions D hM halpha1 baselineRadiusBudget *
        (eta ^ 4 / T.terminalSpacing ^ 4) =
      cmp99SourceMassParameter 1 (M : ℝ) depth *
        T.terminalSpacing⁻¹ ^ 2 := by
  dsimp only
  let T := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
    R C hscale regions D hM halpha1 baselineRadiusBudget
  have hterminal : T.terminalSpacing ≠ 0 := by
    rw [show T.terminalSpacing = (M : ℝ) ^ depth * eta by
      unfold T cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
      rw [regions.weightedQprimeTower_terminalSpacing]]
    exact mul_ne_zero (pow_ne_zero depth (by exact_mod_cast (NeZero.ne M))) heta
  unfold cmp99Eq360C6dSourcePhysicalCountingCoefficient
  exact
    cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient_toWeighted
      T (cmp99SourceMassParameter 1 (M : ℝ) depth) heta hterminal

end

end YangMills.RG
