/-
PRE-VALIDATION -- source present; `.olean` not yet materialized and the
result is not yet compiler-verified.
-/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedActiveLaplacianComplexDictionary
import YangMills.RG.BalabanCMP99SourceFlowFlatQprimeMassComplexDictionary
import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionFibreAction

/-!
# Complex dictionary for the literal source-flow flat precision

The active flat precision is kept as the literal sum of its covariant
Laplacian and source-flow counting-space `Q'^*Q'` mass.  This module consumes
the two independently sealed complex dictionaries and recognizes the exact
full-box complex precision with bare mass zero and weighted coefficient
`a_depth`.

No generated Poincare coefficient, inverse, Green equality or regional bound
is accepted or asserted.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

namespace CMP99SourceGeneratedTerminalComplexFieldData

/-- At every generated active target, the complexification of the literal
source-flow flat precision is the full-box complex precision action with
bare mass zero and the printed coefficient `a_depth`.  Both summands and the
source coefficient are constructed inside the statement. -/
theorem sourceFlowPhysicalPrecision_complexification_eq_fullComplexAction
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth)
    (a : ℝ)
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    let spacing := cmp99SourceGeneratedFullComplexSpacing M (depth + 1)
    let weightedA := cmp99SourceFlowFlatFullComplexA a M depth
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
    let targetBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) target.1
    cmp99SUNLieCoordComplexificationLM Nc
        ((cmp99SourceGaugePrecision
          (cmp99ActiveRegionSourceCovariantLaplacian
            (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
            (matrixSUNAdjointModel Nc)
            (cmp99SourceFlatGaugeConfig d
              (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
            spacing)
          regions.flatExplicitQprime
          (cmp99SourceFlowFlatCountingA d a M depth))
            D.activeField target) =
      cmp99SourceFlatFullComplexPrecisionAction
        (M := M ^ (depth + 1)) (N' := N) 0 weightedA
        D.complexZeroExtension targetBox := by
  dsimp only
  unfold cmp99SourceGaugePrecision
  rw [ContinuousLinearMap.add_apply, PiLp.add_apply, map_add]
  rw [ContinuousLinearMap.smul_apply, PiLp.smul_apply]
  rw [D.activeLaplacian_complexification_eq_fullComplexStencil]
  rw [cmp99SourceFlowCountingMass_complexFieldDictionary]
  simp [cmp99SourceFlatFullComplexPrecisionAction,
    cmp99SourceGeneratedFullComplexBlockSide, complexZeroExtension]

end CMP99SourceGeneratedTerminalComplexFieldData

end

end YangMills.RG
