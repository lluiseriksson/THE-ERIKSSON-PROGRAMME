import tmp.BalabanCMP99Eq360C6dSourceTerminalCoercivity.draft

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# The literal C6d baseline Green is constructed, not supplied

The operator inverted here is exactly the source-fixed C6d baseline precision
from the retained physical tower.  Its positive coercivity floor and witness
are produced by the preceding source theorem.  Consequently the Green, both
inverse identities, its symmetry and its norm bound are all internal; no
Green family or operator-identification equality is caller data.
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

/-- The named literal C6d baseline precision.  Naming the operator once keeps
the inverse and norm statements definitionally tied to the same source
object. -/
noncomputable def cmp99Eq360C6dSourceBaselinePhysicalPrecision :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  let W := R.toCubeWitness C alpha1 hscale
  let T := cmp99Eq360C6dSourceBaselineRetainedPhysicalTower
    R C hscale regions D hM halpha1 baselineRadiusBudget
  let b := cmp99Eq360C6dSourcePhysicalCountingCoefficient
    R C hscale regions D hM halpha1 baselineRadiusBudget
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian Omega
      (matrixSUNAdjointModel Nc) W.transformedBackground eta)
    T.Qprime b

/-- The named precision inherits the source-fixed coercivity theorem without
requesting an operator equality from the caller. -/
theorem isCoerciveCLM_cmp99Eq360C6dSourceBaselinePhysicalPrecision
    (hdepth : 0 < depth)
    (hsmall :
      cmp99SourcePoincareErrorCoeff 4 M depth eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    IsCoerciveCLM
      (cmp99Eq360C6dSourceBaselinePhysicalPrecision
        R C hscale regions D hM halpha1 baselineRadiusBudget)
      (cmp99Eq360C6dSourceBaselinePhysicalCoercivity
        R C hscale regions D hM halpha1 baselineRadiusBudget) := by
  simpa only [cmp99Eq360C6dSourceBaselinePhysicalPrecision] using
    (isCoerciveCLM_cmp99Eq360C6dSourceBaselinePrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)

/-- The literal C6d baseline precision is symmetric because its covariant
Laplacian is symmetric and the retained averaging mass is an adjoint square.
-/
theorem cmp99Eq360C6dSourceBaselinePhysicalPrecision_isSymmetric :
    (cmp99Eq360C6dSourceBaselinePhysicalPrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget).IsSymmetric := by
  unfold cmp99Eq360C6dSourceBaselinePhysicalPrecision
  apply cmp99SourceGaugePrecision_isSymmetric
  exact cmp99ActiveRegionSourceCovariantLaplacian_isSymmetric
    Omega (matrixSUNAdjointModel Nc)
      (R.toCubeWitness C alpha1 hscale).transformedBackground eta

/-- The C6d baseline Green is the canonical inverse of the literal precision,
constructed from the positive source floor and coercivity witness. -/
noncomputable def cmp99Eq360C6dSourceBaselinePhysicalGreen
    (hdepth : 0 < depth)
    (hsmall :
      cmp99SourcePoincareErrorCoeff 4 M depth eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  covarianceOfIsCoerciveCLM
    (cmp99Eq360C6dSourceBaselinePhysicalPrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget)
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)
    (isCoerciveCLM_cmp99Eq360C6dSourceBaselinePhysicalPrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)

/-- The literal precision is a left inverse of the constructed Green. -/
theorem cmp99Eq360C6dSourceBaselinePhysicalPrecision_comp_green
    (hdepth : 0 < depth)
    (hsmall :
      cmp99SourcePoincareErrorCoeff 4 M depth eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    (cmp99Eq360C6dSourceBaselinePhysicalPrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget).comp
        (cmp99Eq360C6dSourceBaselinePhysicalGreen
          R C hscale regions D hM halpha1 baselineRadiusBudget
            hdepth hsmall) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall) _

/-- The constructed Green is a left inverse of the literal precision. -/
theorem cmp99Eq360C6dSourceBaselinePhysicalGreen_comp_precision
    (hdepth : 0 < depth)
    (hsmall :
      cmp99SourcePoincareErrorCoeff 4 M depth eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    (cmp99Eq360C6dSourceBaselinePhysicalGreen
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall).comp
        (cmp99Eq360C6dSourceBaselinePhysicalPrecision
          R C hscale regions D hM halpha1 baselineRadiusBudget) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall) _

/-- The constructed Green has the inverse-coercivity operator-norm bound. -/
theorem norm_cmp99Eq360C6dSourceBaselinePhysicalGreen_le
    (hdepth : 0 < depth)
    (hsmall :
      cmp99SourcePoincareErrorCoeff 4 M depth eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    ‖cmp99Eq360C6dSourceBaselinePhysicalGreen
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall‖ ≤
      (cmp99Eq360C6dSourceBaselinePhysicalCoercivity
        R C hscale regions D hM halpha1 baselineRadiusBudget)⁻¹ := by
  exact norm_covarianceOfIsCoerciveCLM_le _
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall) _

/-- The constructed Green is symmetric because it is the inverse of the
symmetric literal precision. -/
theorem cmp99Eq360C6dSourceBaselinePhysicalGreen_isSymmetric
    (hdepth : 0 < depth)
    (hsmall :
      cmp99SourcePoincareErrorCoeff 4 M depth eta
        (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1) < 1) :
    (cmp99Eq360C6dSourceBaselinePhysicalGreen
      R C hscale regions D hM halpha1 baselineRadiusBudget
        hdepth hsmall).IsSymmetric := by
  exact covarianceOfIsCoerciveCLM_isSymmetric _
    (cmp99Eq360C6dSourceBaselinePhysicalCoercivity_pos
      R C hscale regions D hM halpha1 baselineRadiusBudget
      hdepth R.eta_pos hsmall)
    (isCoerciveCLM_cmp99Eq360C6dSourceBaselinePhysicalPrecision
      R C hscale regions D hM halpha1 baselineRadiusBudget hdepth hsmall)
    (cmp99Eq360C6dSourceBaselinePhysicalPrecision_isSymmetric
      R C hscale regions D hM halpha1 baselineRadiusBudget)

end

end YangMills.RG
