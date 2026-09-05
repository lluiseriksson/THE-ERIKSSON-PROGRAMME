import YangMills.RG.BalabanCMP99Eq342RightAdjointFromValueBound

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- A localized Green value estimate gives the literal right-adjoint estimate
at a caller-supplied terminal spacing. -/
theorem cmp99Eq342_rightAdjoint_blockLocalizedSupBound_at_terminalSpacing
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (background : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {terminalSpacing ell A rate : ℝ}
    (hterminal : 0 < terminalSpacing) (hell : 0 < ell)
    (hG : FinitePiLpTypedBlockLocalizedSupBound G
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (A * ell ^ 2) rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      (G.comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background terminalSpacing).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist
      (648 * A * Real.exp rate * ell ^ 2 / terminalSpacing) rate := by
  have hscaled : 0 < terminalSpacing / ell := div_pos hterminal hell
  have hbase :=
    cmp99Eq342_rightAdjoint_blockLocalizedSupBound_of_value
      (L := L) (K := K) (Q := Q) (Nc := Nc) (depth := depth)
      Omega background G hscaled hell hG
  have hterminal_eq : ell * (terminalSpacing / ell) = terminalSpacing := by
    field_simp [ne_of_gt hell]
  rw [hterminal_eq] at hbase
  convert hbase using 1 <;>
    field_simp [ne_of_gt hterminal, ne_of_gt hell] <;> ring

end

end YangMills.RG
