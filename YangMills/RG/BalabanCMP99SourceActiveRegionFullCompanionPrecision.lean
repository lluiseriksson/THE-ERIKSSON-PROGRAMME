import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecisionCompression
import YangMills.RG.BalabanCMP99SourceActiveRegionTerminalCoercivity

/-!
PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the compiler or axiom oracle.

# Physical precision on the canonical full companion chain

Starting from an arbitrary typed source-region chain, this file constructs
the full companion chain, its terminal `Qprime`, the literal source-flow
counting coefficient and the resulting full-carrier precision.  The same
coefficient is proved equal to the coefficient of the regional tower, and
the full precision compresses exactly to the regional source precision.

At positive depth the full precision inherits the source Poincare coercivity
producer.  No ambient operator, coefficient equality, coercivity witness or
compression equality is caller data.  Reindexing the full active carrier to
the ordinary ambient `FinBox` remains a later dictionary.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The weighted terminal tower generated on the canonical full companion
of a supplied source-region chain. -/
noncomputable def cmp99SourceActiveRegionFullCompanionTower
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc)
      (cmp99SourceFullActiveRegion d N) spacing :=
  (cmp99SourceActiveRegionFullCompanion regions).large.weightedQprimeTower
    hd hM rho spacing epsilon background chain fineSmall

/-- Literal source-flow coefficient in the counting-Hilbert convention on
the full companion tower. -/
noncomputable def cmp99SourceActiveRegionFullCompanionCountingCoefficient
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) : ℝ :=
  cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
    (cmp99SourceActiveRegionFullCompanionTower regions hd hM rho spacing
      epsilon background chain fineSmall)
    (cmp99SourceMassParameter 1 (M : ℝ) depth)

/-- The regional and full-companion towers have exactly the same terminal
spacing, so their counting-Hilbert source coefficients coincide. -/
theorem cmp99SourceActiveRegionFullCompanionCountingCoefficient_eq_regional
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd hM rho
        spacing epsilon background chain fineSmall =
      cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
        (regions.weightedQprimeTower hd hM rho spacing epsilon background chain
          fineSmall)
        (cmp99SourceMassParameter 1 (M : ℝ) depth) := by
  unfold cmp99SourceActiveRegionFullCompanionCountingCoefficient
  unfold cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
  rw [cmp99SourceActiveRegionFullCompanionTower,
    (cmp99SourceActiveRegionFullCompanion regions).large.weightedQprimeTower_terminalSpacing,
    regions.weightedQprimeTower_terminalSpacing]

/-- Full-carrier source precision constructed from the canonical companion,
with the literal source-flow coefficient. -/
noncomputable def cmp99SourceActiveRegionFullCompanionPrecision
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ActiveGaugeZeroCochain (cmp99SourceFullActiveRegion d N)
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain (cmp99SourceFullActiveRegion d N)
        (SUNLieCoord Nc) :=
  let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM rho spacing
    epsilon background chain fineSmall
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99SourceFullActiveRegion d N) rho background spacing)
    T.Qprime
    (cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd hM rho
      spacing epsilon background chain fineSmall)

/-- The constructed full precision compresses exactly to the literal
regional source precision, including equality of the source-flow counting
coefficient. -/
theorem cmp99SourceActiveRegionFullCompanionPrecision_compression
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Tregional := regions.weightedQprimeTower hd hM rho spacing epsilon
      background chain fineSmall
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc) Omega
      (cmp99SourceFullActiveRegion d N)
    let E := cmp99NestedActiveRegionExtension (g := SUNLieCoord Nc) Omega
      (cmp99SourceFullActiveRegion d N)
    R.comp ((cmp99SourceActiveRegionFullCompanionPrecision regions hd hM rho
      spacing epsilon background chain fineSmall).comp E) =
      cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega rho background spacing)
        Tregional.Qprime
        (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient Tregional
          (cmp99SourceMassParameter 1 (M : ℝ) depth)) := by
  let companion := cmp99SourceActiveRegionFullCompanion regions
  have hsub : Omega.sites ⊆
      (cmp99SourceFullActiveRegion d N).sites := by
    intro x _hx
    exact Finset.mem_univ x
  have hcompression := companion.nested.sourceGaugePrecision_compression hsub
    hd hM rho spacing epsilon
    (cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd hM rho
      spacing epsilon background chain fineSmall)
    background chain fineSmall
  rw [cmp99SourceActiveRegionFullCompanionCountingCoefficient_eq_regional
    regions hd hM rho spacing epsilon background chain fineSmall]
  simpa [companion, cmp99SourceActiveRegionFullCompanionPrecision,
    cmp99SourceActiveRegionFullCompanionTower] using hcompression

/-- At positive depth the constructed full companion precision is coercive
with the exact source terminal floor. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionFullCompanionPrecision
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (hdepth : 0 < depth)
    (rho : SUNAdjointModel Nc) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM rho
      spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceActiveRegionFullCompanionPrecision regions hd hM rho spacing
        epsilon background chain fineSmall)
      (cmp99SourceActiveRegionTerminalPhysicalCoercivity T M depth epsilon) := by
  let companion := cmp99SourceActiveRegionFullCompanion regions
  simpa [companion, cmp99SourceActiveRegionFullCompanionPrecision,
    cmp99SourceActiveRegionFullCompanionTower,
    cmp99SourceActiveRegionFullCompanionCountingCoefficient] using
    (isCoerciveCLM_cmp99SourceActiveRegionTerminalPhysicalPrecision
      companion.large hd hM hdepth hspacing background chain fineSmall hsmall)

end

end YangMills.RG
