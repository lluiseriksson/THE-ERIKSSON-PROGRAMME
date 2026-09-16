import YangMills.RG.BalabanCMP99Eq342LaplacianFromLeftDerivativeBound

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.

# Localized covariant Laplacian at an explicit terminal spacing

This adapter keeps the spacing of the literal covariant Laplacian explicit.
It derives the result from the reusable four-direction stencil estimate by
using auxiliary scale `terminalSpacing / ell`; consequently the depth-zero
consumer may pass its literal source spacing without an additional RG factor.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- A localized left-derivative estimate gives the literal covariant
Laplacian estimate at a caller-supplied terminal spacing. -/
theorem cmp99Eq342_laplacian_blockLocalizedSupBound_at_terminalSpacing
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (background : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {terminalSpacing ell leftA rate : ℝ}
    (hterminal : 0 < terminalSpacing) (hell : 0 < ell)
    (hleft : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background terminalSpacing).comp G)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (leftA * ell) rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) background terminalSpacing).comp G)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist
      (4 * leftA * ell *
        ((1 + Real.exp rate) / terminalSpacing)) rate := by
  have hscaled : 0 < terminalSpacing / ell := div_pos hterminal hell
  have hterminal_eq : ell * (terminalSpacing / ell) = terminalSpacing := by
    field_simp [ne_of_gt hell]
  have hleft_scaled : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background
          (ell * (terminalSpacing / ell))).comp G)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (leftA * ell) rate := by
    rw [hterminal_eq]
    exact hleft
  have hbase :=
    cmp99Eq342_laplacian_blockLocalizedSupBound_of_leftDerivative
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := depth)
      Omega background G hscaled hell hleft_scaled
  rw [hterminal_eq] at hbase
  convert hbase using 1 <;>
    field_simp [ne_of_gt hterminal, ne_of_gt hell] <;> ring

end

end YangMills.RG
