import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionZeroDepth

/-!
The Green is not caller data.  It is the canonical covariance of the
Dirichlet compression of the one full-companion ambient precision, using the
literal positive depth-zero counting coefficient `spacing^(-2)` transported
by the preceding module.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ} [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The exact depth-zero regional precision is the Dirichlet compression of
the internally constructed full-companion ambient precision. -/
noncomputable def cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  cmp99SourceAmbientDirichletPrecision Omega
    (cmp99SourceActiveRegionFullCompanionAmbientPrecision regions hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall)

/-- Ambient depth-zero coercivity descends to the exact Dirichlet
compression without changing its literal counting-Hilbert floor. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    IsCoerciveCLM
      (cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero regions hd
        hM spacing epsilon background chain fineSmall)
      (cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd hM
        (matrixSUNAdjointModel Nc) spacing epsilon background chain
        fineSmall) := by
  apply isCoerciveCLM_cmp99SourceAmbientDirichletPrecision
  simpa [cmp99SourceActiveRegionFullCompanionCountingCoefficient] using
    (isCoerciveCLM_cmp99SourceActiveRegionFullCompanionAmbientPrecision_zero
      regions hd hM background chain fineSmall)

/-- Canonical depth-zero Green of the exact regional compression. -/
noncomputable def cmp99SourceActiveRegionFullCompanionDirichletGreen_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  covarianceOfIsCoerciveCLM
    (cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero regions hd hM
      spacing epsilon background chain fineSmall)
    (cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero regions
      hd hM hspacing background chain fineSmall)
    (isCoerciveCLM_cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero
      regions hd hM background chain fineSmall)

/-- The exact regional compression is a left inverse of its generated
depth-zero Green. -/
theorem cmp99SourceActiveRegionFullCompanionDirichletPrecision_comp_green_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero regions hd hM
      spacing epsilon background chain fineSmall).comp
        (cmp99SourceActiveRegionFullCompanionDirichletGreen_zero regions hd hM
          hspacing background chain fineSmall) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero regions
      hd hM hspacing background chain fineSmall) _

/-- The generated depth-zero Green is a left inverse of the exact regional
compression. -/
theorem cmp99SourceActiveRegionFullCompanionDirichletGreen_comp_precision_zero
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (cmp99SourceActiveRegionFullCompanionDirichletGreen_zero regions hd hM
      hspacing background chain fineSmall).comp
        (cmp99SourceActiveRegionFullCompanionDirichletPrecision_zero regions hd
          hM spacing epsilon background chain fineSmall) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero regions
      hd hM hspacing background chain fineSmall) _

/-- Inverse-coercivity operator-norm bound for the generated depth-zero
Dirichlet Green. -/
theorem norm_cmp99SourceActiveRegionFullCompanionDirichletGreen_zero_le
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖cmp99SourceActiveRegionFullCompanionDirichletGreen_zero regions hd hM
      hspacing background chain fineSmall‖ ≤
      (cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd hM
        (matrixSUNAdjointModel Nc) spacing epsilon background chain
        fineSmall)⁻¹ := by
  exact norm_covarianceOfIsCoerciveCLM_le _
    (cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero regions
      hd hM hspacing background chain fineSmall) _

end

end YangMills.RG
