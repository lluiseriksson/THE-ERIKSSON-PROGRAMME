import tmp.BalabanCMP99Eq359OneScaleRealSlice.draft
import tmp.BalabanCMP99ComplexRegionalTower.draft
import YangMills.RG.BalabanCMP99SourceWeightedRegionalTower
import YangMills.RG.BalabanCMP99SourceAdjointTransport

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# A compositional real-slice relation for CMP99 (3.59) towers

The complex and real towers have different scalar fields and therefore
cannot be equated as bundled structures.  This relation carries the canonical
real-linear complexification of the terminal carrier and proves agreement of
both the forward `Qprime` and the independently composed printed-starred
operator.  The `step` constructor consumes the one-scale real-slice theorems;
it accepts no finished tower equality.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : ℕ} [NeZero N] [NeZero Nc]

/-- Real-slice agreement between one analytic tower and one physical
source-weighted tower over the same active region. -/
structure CMP99Eq359TowerRealSliceAgreement
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (complexTower : CMP99ComplexRegionalTower (Nc := Nc) Omega spacing)
    (physicalTower : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc) Omega spacing) where
  terminalComplexification :
    physicalTower.TerminalSpace.carrier →L[ℝ]
      complexTower.TerminalSpace.carrier
  Qprime_realSlice : ∀ phi,
    complexTower.Qprime
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      terminalComplexification (physicalTower.Qprime phi)
  starred_realSlice : ∀ eta,
    complexTower.starred (terminalComplexification eta) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (physicalTower.weightedAdjoint eta)

/-- The two identity towers agree under pointwise complexification. -/
noncomputable def CMP99Eq359TowerRealSliceAgreement.stop
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) :
    CMP99Eq359TowerRealSliceAgreement
      (CMP99ComplexRegionalTower.stop (Nc := Nc) Omega spacing)
      (CMP99SourceWeightedRegionalTower.stop
        (g := SUNLieCoord Nc) Omega spacing) where
  terminalComplexification :=
    cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
  Qprime_realSlice := by
    intro phi
    rfl
  starred_realSlice := by
    intro eta
    rfl

/-- Real-slice agreement is stable under prepending one literal source
average and its printed-starred synthesis.  The physical transport is fixed
to the matrix `SUN` adjoint model and the analytic holonomy is its canonical
`SL(N,C)` image. -/
noncomputable def CMP99Eq359TowerRealSliceAgreement.step
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc)
    (complexTail : CMP99ComplexRegionalTower (Nc := Nc)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing))
    (physicalTail : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing))
    (tailAgreement : CMP99Eq359TowerRealSliceAgreement
      complexTail physicalTail) :
    CMP99Eq359TowerRealSliceAgreement
      (CMP99ComplexRegionalTower.step Omega hOmega spacing
        (cmp99SUNHolonomyToSpecialLinear holonomy) complexTail)
      (CMP99SourceWeightedRegionalTower.step Omega hOmega spacing
        (cmp99AdjointBlockTransport (matrixSUNAdjointModel Nc) holonomy)
        physicalTail) where
  terminalComplexification := tailAgreement.terminalComplexification
  Qprime_realSlice := by
    intro phi
    change complexTail.Qprime
        (cmp99ComplexAdjointBlockAverageCLM Omega
          (cmp99SUNHolonomyToSpecialLinear holonomy)
          (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi)) =
      tailAgreement.terminalComplexification
        (physicalTail.Qprime
          (cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99AdjointBlockTransport (matrixSUNAdjointModel Nc) holonomy)
            phi))
    rw [cmp99ComplexAdjointBlockAverageCLM_realSlice,
      tailAgreement.Qprime_realSlice]
    rfl
  starred_realSlice := by
    intro eta
    change cmp99ComplexAdjointBlockStarSynthesisCLM Omega hOmega
        (cmp99SUNHolonomyToSpecialLinear holonomy)
        (complexTail.starred
          (tailAgreement.terminalComplexification eta)) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
          (cmp99AdjointBlockTransport (matrixSUNAdjointModel Nc) holonomy)
          (physicalTail.weightedAdjoint eta))
    rw [tailAgreement.starred_realSlice,
      cmp99ComplexAdjointBlockStarSynthesisCLM_realSlice]
    rfl

end

end YangMills.RG
