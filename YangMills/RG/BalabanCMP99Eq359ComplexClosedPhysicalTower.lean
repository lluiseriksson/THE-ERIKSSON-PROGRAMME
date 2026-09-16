import YangMills.RG.BalabanCMP99ComplexPhysicalRegionalTower
import YangMills.RG.BalabanCMP99Eq337ComplexClosedRecursiveBackground
import YangMills.RG.BalabanCMP99SourceGeneratedScaledGradient

/-!
# Closed physical analytic tower feeding CMP99 (3.59)

The recursion follows one typed source-region chain.  At every nonterminal
scale it constructs the literal complex `Ubar` successor and immediately
uses that background to construct the next analytic average and its printed
starred synthesis.  No background family, `Qprime` family, starred family or
per-scale radius family is caller data.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable [NeZero (d * (M - 1))]

/-- Private recursion carrying the single closed scalar budget through the
same typed region chain that indexes the analytic average. -/
private noncomputable def cmp99Eq359ComplexClosedPhysicalTowerAux
    (hd : 2 ≤ d) (hM : 2 ≤ M) (r0 R : ℝ)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth r0 R (cmp99UbarNoWindingThreshold Nc)) :
    ∀ {Ncur remaining : ℕ} {Omega : ActiveGaugeRegion d Ncur},
      (regions : CMP99SourceActiveRegionChain d M Ncur Omega remaining) →
      letI : NeZero Ncur := regions.neZero
      (spacing : ℝ) → (k : ℕ) → k + remaining ≤ depth →
      (background : GaugeConfig d Ncur
        (Matrix.SpecialLinearGroup (Fin Nc) ℂ)) →
      (∀ e,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k) →
      CMP99ComplexPhysicalRegionalTower Omega spacing background := by
  intro Ncur remaining Omega regions
  letI : NeZero Ncur := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing k hdepth background hlink
      exact CMP99ComplexPhysicalRegionalTower.stop Omega spacing background
  | @step N' remaining _ Omega hOmega tail ih =>
      intro spacing k hdepth background hlink
      letI : NeZero (M * N') := inferInstance
      have hk : k < depth := by omega
      have hk_le : k ≤ depth := Nat.le_of_lt hk
      let r := cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k
      have hr : 0 ≤ r := (B.radiusAt_nonneg_and_le hk_le).1
      have hnoWinding :
          cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r <
            cmp99UbarNoWindingThreshold Nc := by
        rw [← cmp99ComplexClosedRadiusDeviation_eq_eq337Uniform]
        exact B.deviation_lt_threshold hk
      have hlog :
          cmp99UbarLogRadius
            (cmp99SourceComplexUbarNoWindingBudget
              d M Nc r hnoWinding) < 1 := by
        simpa [r, cmp99ComplexClosedRadiusPhysicalNoWindingBudget] using
          B.physicalLog_lt_one hk
      have hq1 :
          cmp99SourceComplexUbarNextLinkRadius (Nc := Nc) M r
            (cmp99SourceComplexUbarNoWindingBudget
              d M Nc r hnoWinding) < 1 := by
        simpa [r, cmp99ComplexClosedRadiusPhysicalNoWindingBudget] using
          B.physicalNextLink_lt_one hk
      let nextBackground : GaugeConfig d N'
          (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
        cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius
          (d := d) (M := M) (N' := N') (Nc := Nc)
          hd hM background r hr hlink hnoWinding
      have hnext : ∀ e,
          ‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 (k + 1) := by
        intro e
        have hphysical :=
          norm_cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius_sub_one_le
            (d := d) (M := M) (N' := N') (Nc := Nc)
            hd hM background r hr hlink hnoWinding hlog hq1 e
        change ‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ _
        calc
          _ ≤ cmp99SourceComplexUbarNextOrientedLinkRadius (Nc := Nc) M r
              (cmp99SourceComplexUbarNoWindingBudget
                d M Nc r hnoWinding) := hphysical
          _ = cmp99ComplexClosedRadiusAt
              (d * (M - 1)) M r0 (k + 1) := by
            symm
            simpa [r, cmp99ComplexClosedRadiusPhysicalNoWindingBudget] using
              cmp99ComplexClosedRadiusAt_succ_eq_sourceNextOrientedLinkRadius
                d M Nc depth r0 R B k hk
      let tailTower := ih ((M : ℝ) * spacing) (k + 1) (by omega)
        nextBackground hnext
      exact CMP99ComplexPhysicalRegionalTower.step Omega hOmega spacing
        background nextBackground tailTower

/-- Literal source-facing analytic tower for `exp(i eta A') U`.  Its fine
background and every coarse successor are constructed internally from the
physical inputs and one common closed radius budget. -/
noncomputable def cmp99Eq359SourceComplexPerturbedPhysicalTower
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (spacing : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta epsilonU rA R : ℝ)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth
      (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
      R (cmp99UbarNoWindingThreshold Nc)) :
    CMP99ComplexPhysicalRegionalTower Omega spacing
      (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) :=
  cmp99Eq359ComplexClosedPhysicalTowerAux
    (d := d) (M := M) (Nc := Nc) (depth := depth)
    hd hM (cmp99Eq337PhysicalComplexPerturbedLinkRadius
      Nc epsilonU eta rA) R B regions spacing 0 (by omega)
    (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) (by
      intro e
      simpa using
        norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
          U A eta epsilonU rA hA hsmall hU e)

end

end YangMills.RG
