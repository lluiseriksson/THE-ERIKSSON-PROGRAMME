/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalMiddleDecay

/-!
# Exact coordinate transport of the CMP99 equation (3.95) global middle

The generated tower originally bundles its terminal Hilbert space.  This
module proves that transporting both terminal legs to the literal finite
coordinate field yields exactly the coordinate-exposed middle used by the
fixed-rate kernel estimate.  The proof preserves the printed spacing factor
in `Q'`; it introduces no comparison constant.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 4000000 in
/-- The bundled generated middle, transported to terminal coordinates, is
literally the coordinate-exposed middle whose kernel was estimated. -/
theorem cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_transport_eq
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
    let hT := regions.weightedQprimeTower_terminalSpace_eq
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
    let hs := hT.trans hCoord
    cmp99SourceTerminalCLMTransport hs hs Middle =
      cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
        budget fineSmall hsmall := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let hT : T.TerminalSpace = regions.terminalHilbertSpace Nc :=
    regions.weightedQprimeTower_terminalSpace_eq (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  let hCoord : regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) :=
    regions.terminalHilbertSpace_eq_coordinate
  let hs := hT.trans hCoord
  let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  have hterminalEq : T.terminalSpacing =
      (M : ℝ) ^ (depth + 1) * spacing :=
    regions.weightedQprimeTower_terminalSpacing (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hterminal : 0 < T.terminalSpacing := by
    rw [hterminalEq]
    exact mul_pos (pow_pos hMpos _) hspacing
  have hQ := T.Qprime_eq_smul_weightedAdjoint_adjoint hterminal
  have hW := regions.physicalWeightedAdjoint_eq_transported
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) spacing epsilon
    background budget.toRadiusChain fineSmall
  unfold cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
  unfold cmp99SourceTowerCoarseCovarianceMiddle
  unfold cmp99Eq395GeneratedPhysicalMiddle
  dsimp only
  simp only [id_eq]
  change cmp99SourceTerminalCLMTransport hs hs
      (T.Qprime.comp (G.comp (G.comp T.weightedAdjoint))) =
    (cmp99Eq395GeneratedQprimeScale M depth spacing • W.adjoint).comp
      (G.comp (G.comp W))
  let P := cmp99SourcePhysicalTerminalHilbertSpace Nc
    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
  let E' := regions.terminalCoordinateHilbertSpace (Nc := Nc)
  let Wt := cmp99SourceTerminalCLMTransport
      (E := T.TerminalSpace) (F := P) (E' := E') (F' := P)
      hs rfl T.weightedAdjoint
  let Qt := cmp99SourceTerminalCLMTransport
      (E := P) (F := T.TerminalSpace) (E' := P) (F' := E')
      rfl hs T.Qprime
  have hWt : Wt = W := by
    change regions.transportedWeightedAdjoint
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall = W
    exact hW.symm
  have hQt : Qt =
      cmp99Eq395GeneratedQprimeScale M depth spacing • W.adjoint := by
    let a := spacing ^ 4 / T.terminalSpacing ^ 4
    have hQ' : Qt = cmp99SourceTerminalCLMTransport
        (E := P) (F := T.TerminalSpace) (E' := P) (F' := E')
        rfl hs (a • T.weightedAdjoint.adjoint) := by
      exact congrArg (cmp99SourceTerminalCLMTransport
        (E := P) (F := T.TerminalSpace) (E' := P) (F' := E') rfl hs) hQ
    have hsmul := cmp99SourceTerminalCLMTransport_smul
      (E := P) (F := T.TerminalSpace) (E' := P) (F' := E')
      rfl hs a T.weightedAdjoint.adjoint
    have hadj := cmp99SourceTerminalCLMTransport_adjoint
      (E := T.TerminalSpace) (F := P) (E' := E') (F' := P)
      hs rfl T.weightedAdjoint
    calc
      Qt = cmp99SourceTerminalCLMTransport
          (E := P) (F := T.TerminalSpace) (E' := P) (F' := E')
          rfl hs (a • T.weightedAdjoint.adjoint) := hQ'
      _ = a • cmp99SourceTerminalCLMTransport
          (E := P) (F := T.TerminalSpace) (E' := P) (F' := E')
          rfl hs T.weightedAdjoint.adjoint := hsmul
      _ = a • Wt.adjoint := congrArg (fun C => a • C) hadj
      _ = a • W.adjoint := by rw [hWt]; rfl
      _ = cmp99Eq395GeneratedQprimeScale M depth spacing • W.adjoint := by
        dsimp [cmp99Eq395GeneratedQprimeScale, a]
        rw [hterminalEq]
  have hsand : cmp99SourceTerminalCLMTransport hs hs
        (T.Qprime.comp (G.comp (G.comp T.weightedAdjoint))) =
      Qt.comp (G.comp (G.comp Wt)) := by
    exact cmp99SourceTerminalCLMTransport_sandwich
      (E := T.TerminalSpace) (E' := E') (F := P)
      hs T.Qprime G T.weightedAdjoint
  calc
    cmp99SourceTerminalCLMTransport hs hs
        (T.Qprime.comp (G.comp (G.comp T.weightedAdjoint))) =
      Qt.comp (G.comp (G.comp Wt)) := hsand
    _ = (cmp99Eq395GeneratedQprimeScale M depth spacing • W.adjoint).comp
        (G.comp (G.comp W)) := by rw [hQt, hWt]; rfl

end
end YangMills.RG
