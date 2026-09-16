import tmp.P5PhysicalGreenScaleDictionary
import YangMills.RG.BalabanCMP102PhysicalBackgroundBaseBudget

/-!
PRE-VALIDATION: this source is present only in scratch; no `.olean` has been
materialized and the declaration below is not compiler-verified.

# Physical small-background wrapper for CMP89 (2.34)

P0--P5 deliberately retain the source-local pointwise `fineSmall` premise.
At the hRpoly boundary that premise is not caller data: it follows on every
oriented edge from `PhysicalWilsonSmallBackground`.  This wrapper performs
that one-way discharge without importing the CMP102 bridge into the lower
CMP85/CMP89 modules.  The terminal Poincare inequality `hsmall` remains
visible; it is a genuine scalar wall and is not renamed or hidden here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Canonical production of the source-local fine-link bound from the
positive-bond Wilson-small hypothesis.  The factorization `Nfine * 1` is used
only to instantiate the already tracked oriented-edge theorem; it does not
introduce a second blocking scale. -/
def scratch_cmp116PhysicalFineSmall
    (background : PhysicalGaugeBackground 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (epsilon : ℝ)
    (hWilson : PhysicalWilsonSmallBackground background epsilon) :
    ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon :=
  norm_physicalGaugeBackground_apply_sub_one_le
    (M := cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1))
    (N' := 1) background epsilon hWilson

/-- The physical Wilson-small background produces the complete source
fine-link premise internally, so the exact CMP89 (2.34) equality has no
caller-supplied `fineSmall` family. -/
theorem scratch_cmp116PhysicalSeparatedAmbientGreenScaleSum_eq234
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : PhysicalGaugeBackground 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (hWilson : PhysicalWilsonSmallBackground background epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    scratch_cmp89SourceSeparatedAmbientPrefixGreen hL depth hspacing ha
        background budget
          (scratch_cmp116PhysicalFineSmall background epsilon hWilson)
          hsmall =
      scratch_cmp89SourceSeparatedAmbientBaseCovariance hL depth hspacing ha
          background budget
            (scratch_cmp116PhysicalFineSmall background epsilon hWilson)
            hsmall +
        ∑ j : ScratchCMP85PositiveCoarseStep (depth + 1),
          scratch_cmp89SourceSeparatedAmbientGreenIncrement hL depth
            hspacing ha background budget
              (scratch_cmp116PhysicalFineSmall background epsilon hWilson)
              hsmall j := by
  exact scratch_cmp89SourceSeparatedAmbientGreenScaleSum_eq234
    hL depth hspacing ha background budget
      (scratch_cmp116PhysicalFineSmall background epsilon hWilson)
      hsmall

/-- Physical source-facing form of CMP89 (2.34).  Besides discharging
`fineSmall`, this endpoint keeps the exact `a_j^2 * spacing_j^(-4)` factor and
the `G_j Q_j^dagger C^(j) Q_j G_j` order visible in its conclusion. -/
theorem scratch_cmp116PhysicalSeparatedAmbientGreenScaleSum_eq234_literal
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : PhysicalGaugeBackground 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (hWilson : PhysicalWilsonSmallBackground background epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1) :
    let fineSmall := scratch_cmp116PhysicalFineSmall background epsilon hWilson
    let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
    scratch_cmp89SourceSeparatedAmbientPrefixGreen hL depth hspacing ha
        background budget fineSmall hsmall =
      scratch_cmp89SourceSeparatedAmbientBaseCovariance hL depth hspacing ha
          background budget fineSmall hsmall +
        ∑ j : ScratchCMP85PositiveCoarseStep (depth + 1),
          let T := scratch_cmp85SourceGeneratedPrefixTower
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) spacing epsilon background budget.toRadiusChain
            fineSmall
          let r := j.currentPrefix
          let Qj := (T.towerAt r.1).Qprime
          let Qjdag := (T.towerAt r.1).weightedAdjoint
          let Gj := scratch_cmp85SourceGeneratedPrefixGreen
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) hspacing ha 0 background budget.toRadiusChain
            fineSmall hsmall r
          let Cj := scratch_cmp85SourceGeneratedCoarseCovariance
            (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
            (by norm_num) hL
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1) hspacing ha 0 background budget.toRadiusChain
            fineSmall hsmall j
          finitePiLpTypedKernelReindex e e
            ((cmp99SourceMassParameter a (L : ℝ) (r.1.val - 1)) ^ 2 *
                (T.towerAt r.1).terminalSpacing⁻¹ ^ 4 •
              Gj.comp (Qjdag.comp (Cj.comp (Qj.comp Gj)))) := by
  dsimp only
  exact scratch_cmp89SourceSeparatedAmbientGreenScaleSum_eq234_literal
    hL depth hspacing ha background budget
      (scratch_cmp116PhysicalFineSmall background epsilon hWilson) hsmall

end

end YangMills.RG
