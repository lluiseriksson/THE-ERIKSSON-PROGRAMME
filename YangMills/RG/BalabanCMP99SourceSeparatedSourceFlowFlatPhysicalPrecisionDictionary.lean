/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlowFlatPrecisionScalarDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernel

/-!
# Real source-flow flat physical precision dictionary

The final CMP85 positive-prefix precision is identified with the literal flat
precision built from the terminal explicit `Q'` and the source-flow counting
coefficient.  This is a real operator bridge only: no complexification,
inverse identification, regional bound or window-15 attainment is asserted.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Literal real source-flow precision on the final generated active carrier.
The bare mass is zero and the source coefficient is in counting coordinates. -/
noncomputable def cmp99SourceSeparatedSourceFlowFlatFinePrecisionExplicit
    (depth : ℕ) (a : ℝ) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1))
        (SUNLieCoord Nc) :=
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := L) Omega (depth + 1)
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
      (matrixSUNAdjointModel Nc)
      (cmp99SourceFlatGaugeConfig 4
        (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)))
    regions.flatExplicitQprime
    (cmp99SourceFlowFlatCountingA 4 a L depth)

/-- The final positive-prefix precision is exactly the literal source-flow
flat precision with explicit terminal `Q'`. -/
theorem cmp89SourceSeparatedFinePrefixPrecision_eq_sourceFlowExplicit
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ) :
    cmp89SourceSeparatedFinePrefixPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        hL depth
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0 a
        (cmp99SourceFlatGaugeConfig 4
          (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc)
        (cmp99SourceFlatZeroClosedBudget
          (d := 4) (M := L) (Nc := Nc) (depth + 1))
        cmp99SourceFlatGaugeConfig_zero_small =
      cmp99SourceSeparatedSourceFlowFlatFinePrecisionExplicit
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth a := by
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let spacing := cmp99SourceGeneratedFullComplexSpacing L (depth + 1)
  let background := cmp99SourceFlatGaugeConfig 4
    (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) Nc
  let chain := cmp99SourceFlatZeroRadiusChain
    (d := 4) (M := L) (Nc := Nc) (depth + 1)
  let fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0 :=
    cmp99SourceFlatGaugeConfig_zero_small
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := L) Omega (depth + 1)
  let Tprefix := cmp85SourceGeneratedPrefixTower
    (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
    (by norm_num) hL Omega (depth + 1) spacing 0 background chain fineSmall
  let Tterminal := regions.weightedQprimeTower
    (by norm_num) hL (matrixSUNAdjointModel Nc) spacing 0 background chain
      fineSmall
  have hlast : Tprefix.towerAt (Fin.last (depth + 1)) = Tterminal := by
    simpa only [Tprefix, Tterminal, cmp85SourceGeneratedPrefixTower] using
      (cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
        (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
        (by norm_num) hL (matrixSUNAdjointModel Nc) Omega
        (depth + 1) spacing 0 background chain fineSmall)
  let hT : Tterminal.TerminalSpace = regions.terminalHilbertSpace Nc :=
    regions.weightedQprimeTower_terminalSpace_eq
      (by norm_num) hL (matrixSUNAdjointModel Nc) spacing 0 background chain
        fineSmall
  let hCoord : regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) :=
    regions.terminalHilbertSpace_eq_coordinate
  let Qtransported := cmp99SourceTerminalCLMTransport
    (E := cmp99SourcePhysicalTerminalHilbertSpace Nc
      (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)))
    (F := Tterminal.TerminalSpace)
    (E' := cmp99SourcePhysicalTerminalHilbertSpace Nc
      (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)))
    (F' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
    rfl (hT.trans hCoord) Tterminal.Qprime
  have hphysical := regions.physicalQprime_eq_transported
    (by norm_num) hL (matrixSUNAdjointModel Nc) spacing 0 background chain
      fineSmall
  have hflat := regions.flatPhysicalQprime_eq_explicit
    (by norm_num) hL (matrixSUNAdjointModel Nc) spacing
  have hQ : regions.transportedQprime
      (by norm_num) hL (matrixSUNAdjointModel Nc) spacing 0 background chain
        fineSmall = regions.flatExplicitQprime := by
    calc
      _ = regions.physicalQprime
          (by norm_num) hL (matrixSUNAdjointModel Nc) spacing 0 background chain
            fineSmall := hphysical.symm
      _ = regions.flatPhysicalQprime
          (by norm_num) hL (matrixSUNAdjointModel Nc) spacing := rfl
      _ = regions.flatExplicitQprime := hflat
  have hQtransported : Qtransported = regions.flatExplicitQprime := hQ
  have htransported : Qtransported.adjoint.comp Qtransported =
      Tterminal.Qprime.adjoint.comp Tterminal.Qprime := by
    exact cmp99SourceTerminalCLMTransport_adjoint_comp_self
      (E := cmp99SourcePhysicalTerminalHilbertSpace Nc
        (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)))
      (F := Tterminal.TerminalSpace)
      (F' := regions.terminalCoordinateHilbertSpace (Nc := Nc))
      (hT.trans hCoord) Tterminal.Qprime
  have hmass : Tterminal.Qprime.adjoint.comp Tterminal.Qprime =
      regions.flatExplicitQprime.adjoint.comp regions.flatExplicitQprime := by
    calc
      Tterminal.Qprime.adjoint.comp Tterminal.Qprime =
          Qtransported.adjoint.comp Qtransported := htransported.symm
      _ = regions.flatExplicitQprime.adjoint.comp
          regions.flatExplicitQprime :=
        congrArg (fun R => R.adjoint.comp R) hQtransported
  have hcoeff : cmp85SourcePrefixCountingCoefficient Tprefix a
      (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)) =
        cmp99SourceFlowFlatCountingA 4 a L depth :=
    cmp85LastPositivePrefix_sourceFlow_countingCoefficient_eq depth a Tprefix
  change cmp99SourceGaugePrecision
      (cmp85BareMassPrecision
        (cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing) 0)
      (Tprefix.towerAt
        (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)).1).Qprime
      (cmp85SourcePrefixCountingCoefficient Tprefix a
        (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))) =
    cmp99SourceGaugePrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
        (matrixSUNAdjointModel Nc) background spacing)
      regions.flatExplicitQprime
      (cmp99SourceFlowFlatCountingA 4 a L depth)
  have hlastPrefix :
      (cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)).1 =
        Fin.last (depth + 1) := rfl
  rw [hlastPrefix, hlast, hcoeff]
  unfold cmp85BareMassPrecision cmp99SourceGaugePrecision
  rw [hmass]
  simp only [pow_two, zero_mul, zero_smul, add_zero]

/-- Ambient form of the same real dictionary, through the already sealed
source-separated full-site equivalence. -/
theorem cmp99SourceSeparatedSourceFlowFlatAmbientPrecision_eq_reindexExplicit
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ) :
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a =
      finitePiLpTypedKernelReindex
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth)
        (cmp99SourceSeparatedSourceFlowFlatFinePrecisionExplicit
          (L := L) (K := K) (Q := Q) (Nc := Nc) depth a) := by
  unfold cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
  unfold cmp89SourceSeparatedAmbientPrefixPrecision
  rw [cmp89SourceSeparatedFinePrefixPrecision_eq_sourceFlowExplicit]

end

end YangMills.RG
