import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized in a fresh cold checkout, and the result is not compiler-verified for sealing.  Exact depth-zero companion coercivity.  This source
has no compiler or axiom-oracle verdict.

The positive-depth Poincare floor vanishes at depth zero and is not used
here.  The terminal average is the identity, while the literal physical
counting coefficient remains `spacing^(-2)` after the source normalization.
The regional, full-companion and ambient coercivity statements are therefore
transported from the existing exact base-case theorem rather than obtained
by specializing a positive-depth quotient.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Exact depth-zero coercivity of the internally constructed full-companion
precision.  Its floor is the literal physical counting coefficient, not one
and not the positive-depth Poincare expression. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionFullCompanionPrecision_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceActiveRegionFullCompanionPrecision regions hd hM
        (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall)
      (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
        (cmp99SourceMassParameter 1 (M : ℝ) 0)) := by
  let companion := cmp99SourceActiveRegionFullCompanion regions
  simpa [companion, cmp99SourceActiveRegionFullCompanionPrecision,
    cmp99SourceActiveRegionFullCompanionTower,
    cmp99SourceActiveRegionFullCompanionCountingCoefficient] using
    (isCoerciveCLM_cmp99SourceActiveRegionTerminalPhysicalPrecision_zero
      companion.large hd hM background chain fineSmall)

/-- The exact depth-zero full-companion coefficient is strictly positive at
positive source spacing. -/
theorem cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    0 < cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall := by
  let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM
    (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
  have hMreal : (0 : ℝ) < M := by
    exact_mod_cast (NeZero.pos M)
  have ha : 0 < cmp99SourceMassParameter 1 (M : ℝ) 0 :=
    cmp99SourceMassParameter_pos (by norm_num) hMreal 0
  have hterminal : 0 < T.terminalSpacing := by
    change 0 <
      ((cmp99SourceActiveRegionFullCompanion regions).large.weightedQprimeTower
        hd hM (matrixSUNAdjointModel Nc) spacing epsilon background chain
        fineSmall).terminalSpacing
    rw [(cmp99SourceActiveRegionFullCompanion regions).large.weightedQprimeTower_terminalSpacing]
    exact mul_pos (pow_pos hMreal 0) hspacing
  unfold cmp99SourceActiveRegionFullCompanionCountingCoefficient
  exact cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient_pos
    T ha hspacing hterminal

/-- Reindexing the full carrier to the ordinary ambient finite box preserves
the exact depth-zero floor. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionFullCompanionAmbientPrecision_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceActiveRegionFullCompanionAmbientPrecision regions hd hM
        (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall)
      (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
        (cmp99SourceMassParameter 1 (M : ℝ) 0)) := by
  exact isCoerciveCLM_finitePiLpTypedKernelReindex
    (ι := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
    (ι' := FinBox d N)
    (g := SUNLieCoord Nc)
    (cmp99SourceFullActiveRegionSiteEquiv d N)
    (cmp99SourceActiveRegionFullCompanionPrecision
      (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega) (depth := 0)
      regions hd hM (matrixSUNAdjointModel Nc) spacing epsilon background chain
      fineSmall)
    (isCoerciveCLM_cmp99SourceActiveRegionFullCompanionPrecision_zero
      (d := d) (M := M) (N := N) (Nc := Nc) (Omega := Omega)
      regions hd hM background chain fineSmall)

end

end YangMills.RG
