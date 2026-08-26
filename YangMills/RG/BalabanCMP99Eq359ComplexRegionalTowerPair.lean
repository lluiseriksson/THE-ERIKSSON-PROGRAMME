import YangMills.RG.BalabanCMP99ComplexRegionalTower

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Common-target two-tower algebra for CMP99 (3.59)

Baseline and perturbed recursions share one terminal type by construction.
Their forward and printed-starred differences are therefore literal operator
subtractions; no target identification or caller-supplied `F2` is needed.
-/

namespace YangMills.RG

noncomputable section

/-- A common-target pair of analytic regional towers. -/
structure CMP99Eq359ComplexRegionalTowerPair
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) where
  depth : ℕ
  TerminalSpace : CMP99ComplexTowerHilbertSpace
  terminalSpacing : ℝ
  Q0 Q1 : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
    TerminalSpace.carrier
  starred0 starred1 : TerminalSpace.carrier →L[ℂ]
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc)

/-- Empty pair: both recursions are the identity on the common carrier. -/
noncomputable def CMP99Eq359ComplexRegionalTowerPair.stop
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ) :
    CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing where
  depth := 0
  TerminalSpace := {
    carrier := ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) }
  terminalSpacing := spacing
  Q0 := ContinuousLinearMap.id ℂ _
  Q1 := ContinuousLinearMap.id ℂ _
  starred0 := ContinuousLinearMap.id ℂ _
  starred1 := ContinuousLinearMap.id ℂ _

/-- Add one baseline/perturbed source scale on the same typed carrier. -/
noncomputable def CMP99Eq359ComplexRegionalTowerPair.step
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (holonomy0 holonomy1 : FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (tail : CMP99Eq359ComplexRegionalTowerPair (Nc := Nc)
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing)) :
    CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing where
  depth := tail.depth + 1
  TerminalSpace := tail.TerminalSpace
  terminalSpacing := tail.terminalSpacing
  Q0 := tail.Q0.comp (cmp99ComplexAdjointBlockAverageCLM Omega holonomy0)
  Q1 := tail.Q1.comp (cmp99ComplexAdjointBlockAverageCLM Omega holonomy1)
  starred0 :=
    (cmp99ComplexAdjointBlockStarSynthesisCLM Omega hOmega holonomy0).comp
      tail.starred0
  starred1 :=
    (cmp99ComplexAdjointBlockStarSynthesisCLM Omega hOmega holonomy1).comp
      tail.starred1

/-- Literal analytic `F'_2(A) = Q'(exp(i eta A')U) - Q'(U)`. -/
def CMP99Eq359ComplexRegionalTowerPair.F2
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      T.TerminalSpace.carrier :=
  T.Q1 - T.Q0

/-- Independently constructed printed starred difference.  This is not
`F2.adjoint` away from the compact real slice. -/
def CMP99Eq359ComplexRegionalTowerPair.F2star
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing) :
    T.TerminalSpace.carrier →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  T.starred1 - T.starred0

@[simp] theorem CMP99Eq359ComplexRegionalTowerPair.Q1_eq_Q0_add_F2
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing) :
    T.Q1 = T.Q0 + T.F2 := by
  apply ContinuousLinearMap.ext
  intro phi
  simp [CMP99Eq359ComplexRegionalTowerPair.F2]

@[simp] theorem CMP99Eq359ComplexRegionalTowerPair.starred1_eq_starred0_add_F2star
    {d N Nc : ℕ} [NeZero N] [NeZero Nc]
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing) :
    T.starred1 = T.starred0 + T.F2star := by
  apply ContinuousLinearMap.ext
  intro eta
  simp [CMP99Eq359ComplexRegionalTowerPair.F2star]

end

end YangMills.RG
