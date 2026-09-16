import YangMills.RG.BalabanCMP99SourceEq395TerminalReindex

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

universe u

theorem test_terminalTransport_apply_heq
    {E F E' F' : CMP99SourceWeightedTowerHilbertSpace}
    (hE : E = E') (hF : F = F')
    (C : E.carrier →L[ℝ] F.carrier)
    {x : E.carrier} {x' : E'.carrier} (hx : HEq x x') :
    HEq (C x) (cmp99SourceTerminalCLMTransport hE hF C x') := by
  subst E'
  subst F'
  exact congrArg C (eq_of_heq hx) |>.heq

theorem test_piLpCongrLeft_cast_heq
    {ι ι' : Type u} {g : Type*} [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (h : ι = ι') (f : FinitePiLpField ι g) :
    HEq ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
      (Equiv.cast h)).toContinuousLinearEquiv f) f := by
  subst ι'
  rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem test_onSource_eq_transport
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
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
    let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
    let hPhys :=
      cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
        (Nc := Nc) (M := M) Omega (depth + 1)
    let h := hCoord.symm.trans hPhys
    cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
        background budget fineSmall hsmall =
      cmp99SourceTerminalCLMTransport h h
        (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
          budget fineSmall hsmall) := by
  apply ContinuousLinearMap.ext
  intro f
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhys :=
    cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
      (Nc := Nc) (M := M) Omega (depth + 1)
  let h := hCoord.symm.trans hPhys
  let G := cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing
    background budget fineSmall hsmall
  let sourceBack :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (Equiv.cast hsite).symm).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (Equiv.cast hsite)).toContinuousLinearEquiv
  change targetMap (G (sourceBack f)) =
    cmp99SourceTerminalCLMTransport h h G f
  have hback : HEq (sourceBack f) f := by
    simpa only [sourceBack, Equiv.cast_symm] using
      (test_piLpCongrLeft_cast_heq hsite.symm f)
  have hG : HEq (G (sourceBack f))
      (cmp99SourceTerminalCLMTransport h h G f) :=
    test_terminalTransport_apply_heq h h G hback
  have hforward : HEq (targetMap (G (sourceBack f)))
      (G (sourceBack f)) := by
    exact test_piLpCongrLeft_cast_heq hsite (G (sourceBack f))
  exact eq_of_heq (hforward.trans hG)

end
end YangMills.RG
