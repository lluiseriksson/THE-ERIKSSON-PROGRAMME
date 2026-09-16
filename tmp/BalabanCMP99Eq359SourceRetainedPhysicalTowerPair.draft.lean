import YangMills.RG.BalabanCMP99Eq359ComplexClosedPhysicalTowerPair
import YangMills.RG.BalabanCMP99SourceRetainedFineExtension
import YangMills.RG.BalabanCMP99SourceRetainedFineOneCochainExtension

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# A retained-source analytic tower pair for the C6d Eq. (3.60) boundary

Both averaging branches are generated from the canonical retained extension.
The physical perturbing one-cochain is extended by zero and complexified
internally.  The caller supplies only scalar smallness gates; it cannot choose
either analytic tower, a complex perturbation, `F2`, or `F2star`.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable [NeZero (d * (M - 1))]

/-- The common-target Eq. (3.59) pair on the retained physical read carrier.
The complex one-cochain appearing in the output is definitionally the
complexification of the source-closed physical extension. -/
noncomputable def
    CMP99SourceActiveRegionChain.retainedComplexClosedPhysicalTowerPair
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (spacing : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (eta epsilonU rA R : ℝ) (hepsilonU : 0 ≤ epsilonU) (hrA : 0 ≤ rA)
    (hA : ∀ b, ‖regions.retainedFineComplexOneCochain A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(U (positiveEdgeOfPhysicalBond q) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth
      (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
      R (cmp99UbarNoWindingThreshold Nc)) :
    CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing := by
  let retainedU := regions.retainedFineExtension U
  let retainedA := regions.retainedFineComplexOneCochain A
  have retainedU_small : ∀ b,
      ‖(retainedU (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU := by
    intro b
    exact regions.norm_retainedFineExtension_sub_one_le
      U epsilonU hepsilonU hU (positiveEdgeOfPhysicalBond b)
  exact cmp99Eq359SourceComplexClosedPhysicalTowerPair
    regions hd hM spacing retainedU retainedA eta epsilonU rA R hrA hA
      hsmall retainedU_small B

end

end YangMills.RG
