import tmp.BalabanCMP99ComplexTransportedBlockAverage.draft

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Finite analytic `Q'`/starred recursion for CMP99 (3.59)

The two operators are composed from the literal one-scale analytic factors.
The forward average uses printed order; the independently constructed
starred synthesis uses reverse order.  No terminal `Qprime`, starred operator
or equality between independently chosen towers is accepted by `step`.
-/

namespace YangMills.RG

noncomputable section

/-- Bundled terminal complex Hilbert space for the varying regional tower. -/
structure CMP99ComplexTowerHilbertSpace where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]
  [finiteDimensional : FiniteDimensional ℂ carrier]

attribute [instance]
  CMP99ComplexTowerHilbertSpace.normedAddCommGroup
  CMP99ComplexTowerHilbertSpace.innerProductSpace
  CMP99ComplexTowerHilbertSpace.completeSpace
  CMP99ComplexTowerHilbertSpace.finiteDimensional

/-- Analytic regional tower with forward and printed-starred operators kept
as independent internally composed data. -/
structure CMP99ComplexRegionalTower
    {d N : ℕ} {Nc : ℕ} [NeZero N] [NeZero Nc]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) where
  depth : ℕ
  TerminalSpace : CMP99ComplexTowerHilbertSpace
  terminalSpacing : ℝ
  Qprime : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
    TerminalSpace.carrier
  starred : TerminalSpace.carrier →L[ℂ]
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc)

/-- Empty analytic composition. -/
noncomputable def CMP99ComplexRegionalTower.stop
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) :
    CMP99ComplexRegionalTower (Nc := Nc) Omega spacing where
  depth := 0
  TerminalSpace := {
    carrier := ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) }
  terminalSpacing := spacing
  Qprime := ContinuousLinearMap.id ℂ _
  starred := ContinuousLinearMap.id ℂ _

/-- Prepend one source-normalized analytic factor.  The forward order is
`Q_tail.comp Q_head`; the printed star is `Q_head^star.comp Q_tail^star`. -/
noncomputable def CMP99ComplexRegionalTower.step
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (tail : CMP99ComplexRegionalTower (Nc := Nc)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    CMP99ComplexRegionalTower (Nc := Nc) Omega spacing where
  depth := tail.depth + 1
  TerminalSpace := tail.TerminalSpace
  terminalSpacing := tail.terminalSpacing
  Qprime := tail.Qprime.comp
    (cmp99ComplexAdjointBlockAverageCLM Omega holonomy)
  starred :=
    (cmp99ComplexAdjointBlockStarSynthesisCLM Omega hOmega holonomy).comp
      tail.starred

@[simp] theorem CMP99ComplexRegionalTower.depth_stop
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) :
    (CMP99ComplexRegionalTower.stop (Nc := Nc) Omega spacing).depth = 0 := rfl

theorem CMP99ComplexRegionalTower.depth_step
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (tail : CMP99ComplexRegionalTower (Nc := Nc)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    (CMP99ComplexRegionalTower.step Omega hOmega spacing holonomy tail).depth =
      tail.depth + 1 := rfl

theorem CMP99ComplexRegionalTower.Qprime_step
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (tail : CMP99ComplexRegionalTower (Nc := Nc)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    (CMP99ComplexRegionalTower.step Omega hOmega spacing holonomy tail).Qprime =
      tail.Qprime.comp
        (cmp99ComplexAdjointBlockAverageCLM Omega holonomy) := rfl

theorem CMP99ComplexRegionalTower.starred_step
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (holonomy : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (tail : CMP99ComplexRegionalTower (Nc := Nc)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    (CMP99ComplexRegionalTower.step Omega hOmega spacing holonomy tail).starred =
      (cmp99ComplexAdjointBlockStarSynthesisCLM Omega hOmega holonomy).comp
        tail.starred := rfl

end

end YangMills.RG
