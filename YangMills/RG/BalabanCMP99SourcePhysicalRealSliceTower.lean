import YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice
import YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement
import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime

/-!
# A source-generated CMP99 (3.59) tower on the physical real slice

This recursion constructs the analytic tower from the canonical complex
images of the same physical `Ubar` backgrounds that construct the weighted
physical tower.  Its agreement certificate is built scale by scale.  No
terminal operator equality or family of intermediate backgrounds is input.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Analytic tower obtained by complexifying each internally generated
physical background in the literal source recursion. -/
noncomputable def CMP99SourceActiveRegionChain.physicalRealSliceComplexTower
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    (spacing epsilon : ℝ) → (background : PhysicalGaugeBackground d N Nc) →
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon) →
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) →
    CMP99ComplexPhysicalRegionalTower Omega spacing
      (cmp99PhysicalGaugeBackgroundToSpecialLinear background) := by
  letI : NeZero N := regions.neZero
  intro spacing epsilon background chain fineSmall
  induction regions generalizing spacing epsilon with
  | stop Omega =>
      exact CMP99ComplexPhysicalRegionalTower.stop Omega spacing
        (cmp99PhysicalGaugeBackgroundToSpecialLinear background)
  | @step N' depth _ Omega hOmega tail ih =>
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      exact CMP99ComplexPhysicalRegionalTower.step Omega hOmega spacing
        (cmp99PhysicalGaugeBackgroundToSpecialLinear background)
        (cmp99PhysicalGaugeBackgroundToSpecialLinear
          Scale.toSourceScale.data.nextBackground)
        (ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon)
          Scale.toSourceScale.data.nextBackground chain.tail nextSmall)

/-- The generated analytic real-slice tower agrees with the literal physical
weighted tower at `matrixSUNAdjointModel Nc`.  The relation is built by the
sealed one-scale theorem and the exact shared physical contour. -/
noncomputable def CMP99SourceActiveRegionChain.physicalRealSliceTowerAgreement
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    letI : NeZero N := regions.neZero
    ∀ (spacing epsilon : ℝ) (background : PhysicalGaugeBackground d N Nc)
      (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
      (fineSmall : ∀ e : ConcreteEdge d N,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon),
      CMP99Eq359TowerRealSliceAgreement
        (regions.physicalRealSliceComplexTower hd hM spacing epsilon
          background chain fineSmall).toComplexTower
        (regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
          spacing epsilon background chain fineSmall) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing epsilon background chain fineSmall
      exact CMP99Eq359TowerRealSliceAgreement.stop Omega spacing
  | @step N' depth _ Omega hOmega tail ih =>
      intro spacing epsilon background chain fineSmall
      letI : NeZero (M * N') := inferInstance
      let Scale : CMP99SourceNormalizedRegionalScale Omega background :=
        CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM Omega background
          hOmega epsilon chain.epsilon_nonneg chain.head_noWinding fineSmall
      have nextSmall : ∀ e : ConcreteEdge d N',
          ‖(Scale.toSourceScale.data.nextBackground e :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99SourceUbarNextFineRadius d M epsilon := by
        intro e
        simpa [Scale, CMP99SourceNormalizedRegionalScale.ofFineSmall,
          CMP99SourceRegionalScale.ofFineSmall] using
          norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
            hd hM Omega background (cmp99SourceBlockAverageWeight M d)
            epsilon chain.epsilon_nonneg chain.head_noWinding
            chain.head_logSmall fineSmall e
      let tailAgreement := ih ((M : ℝ) * spacing)
        (cmp99SourceUbarNextFineRadius d M epsilon)
        Scale.toSourceScale.data.nextBackground chain.tail nextSmall
      change CMP99Eq359TowerRealSliceAgreement
        (CMP99ComplexRegionalTower.step Omega hOmega spacing
          (cmp99ComplexPhysicalBlockHolonomy
            (cmp99PhysicalGaugeBackgroundToSpecialLinear background))
          (tail.physicalRealSliceComplexTower hd hM
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail
            nextSmall).toComplexTower)
        (CMP99SourceWeightedRegionalTower.step Omega hOmega spacing
          (cmp99SourceWeightedPhysicalTransport
            (matrixSUNAdjointModel Nc) background)
          (tail.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall))
      simpa only [cmp99SourceWeightedPhysicalTransport,
        cmp99ComplexPhysicalBlockHolonomy_realSlice] using
        (CMP99Eq359TowerRealSliceAgreement.step Omega hOmega spacing
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) background)
          ((tail.physicalRealSliceComplexTower hd hM
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall).toComplexTower)
          (tail.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon)
            Scale.toSourceScale.data.nextBackground chain.tail nextSmall)
          tailAgreement)

end

end YangMills.RG
