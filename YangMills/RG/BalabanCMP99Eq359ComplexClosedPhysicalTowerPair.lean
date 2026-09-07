import YangMills.RG.BalabanCMP99Eq359ComplexRegionalTowerPair
import YangMills.RG.BalabanCMP99ComplexPhysicalRegionalTower
import YangMills.RG.BalabanCMP99Eq337ComplexClosedRecursiveBackground
import YangMills.RG.BalabanCMP99SourceGeneratedScaledGradient

/-!
# Closed source-specific two-tower producer for CMP99 (3.59)

Baseline and perturbed complex backgrounds are advanced together through one
typed source-region chain and one common closed radius envelope.  Every
coarse background, contour holonomy, forward average and printed-starred
synthesis is constructed inside the recursion.  The caller cannot supply
`Q0`, `Q1`, `F2`, `F2star` or a family of intermediate backgrounds.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable [NeZero (d * (M - 1))]

/-- Private paired fine-to-coarse recursion.  Both branches use the same
generated radius at each scale, so their terminal operator types agree by
construction rather than by a supplied equivalence. -/
private noncomputable def cmp99Eq359ComplexClosedPhysicalTowerPairAux
    (hd : 2 ≤ d) (hM : 2 ≤ M) (r0 R : ℝ)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth r0 R (cmp99UbarNoWindingThreshold Nc)) :
    ∀ {Ncur remaining : ℕ} {Omega : ActiveGaugeRegion d Ncur},
      (regions : CMP99SourceActiveRegionChain d M Ncur Omega remaining) →
      letI : NeZero Ncur := regions.neZero
      (spacing : ℝ) → (k : ℕ) → k + remaining ≤ depth →
      (background0 background1 : GaugeConfig d Ncur
        (Matrix.SpecialLinearGroup (Fin Nc) ℂ)) →
      (∀ e,
        ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k) →
      (∀ e,
        ‖(background1 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k) →
      CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing := by
  intro Ncur remaining Omega regions
  letI : NeZero Ncur := regions.neZero
  induction regions with
  | stop Omega =>
      intro spacing k hdepth background0 background1 hlink0 hlink1
      exact CMP99Eq359ComplexRegionalTowerPair.stop Omega spacing
  | @step N' remaining _ Omega hOmega tail ih =>
      intro spacing k hdepth background0 background1 hlink0 hlink1
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
      let next0 : GaugeConfig d N'
          (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
        cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius
          (d := d) (M := M) (N' := N') (Nc := Nc)
          hd hM background0 r hr hlink0 hnoWinding
      let next1 : GaugeConfig d N'
          (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
        cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius
          (d := d) (M := M) (N' := N') (Nc := Nc)
          hd hM background1 r hr hlink1 hnoWinding
      have hnext0 : ∀ e,
          ‖(next0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 (k + 1) := by
        intro e
        have hphysical :=
          norm_cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius_sub_one_le
            (d := d) (M := M) (N' := N') (Nc := Nc)
            hd hM background0 r hr hlink0 hnoWinding hlog hq1 e
        change ‖(next0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ _
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
      have hnext1 : ∀ e,
          ‖(next1 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 (k + 1) := by
        intro e
        have hphysical :=
          norm_cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius_sub_one_le
            (d := d) (M := M) (N' := N') (Nc := Nc)
            hd hM background1 r hr hlink1 hnoWinding hlog hq1 e
        change ‖(next1 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ _
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
      let tailPair := ih ((M : ℝ) * spacing) (k + 1) (by omega)
        next0 next1 hnext0 hnext1
      exact CMP99Eq359ComplexRegionalTowerPair.step Omega hOmega spacing
        (cmp99ComplexPhysicalBlockHolonomy background0)
        (cmp99ComplexPhysicalBlockHolonomy background1) tailPair

/-- Source-facing Eq. (3.59) pair.  The baseline is the literal zero
perturbation of `U`; the perturbed branch is `exp(i eta A') U`.  Both consume
the same conservative radius envelope, giving a common target without an
operator cast. -/
noncomputable def cmp99Eq359SourceComplexClosedPhysicalTowerPair
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (spacing : ℝ)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta epsilonU rA R : ℝ) (hrA : 0 ≤ rA)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth
      (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
      R (cmp99UbarNoWindingThreshold Nc)) :
    CMP99Eq359ComplexRegionalTowerPair (Nc := Nc) Omega spacing := by
  let background0 := cmp99Eq337PhysicalComplexPerturbedBackground U A 0
  let background1 := cmp99Eq337PhysicalComplexPerturbedBackground U A eta
  have hsmall0 : |(0 : ℝ)| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2 := by
    norm_num
  have hbase0 : ∀ e,
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU 0 rA := by
    intro e
    simpa [background0] using
      norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
        U A 0 epsilonU rA hA hsmall0 hU e
  have hradius_mono :
      cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU 0 rA ≤
        cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
    unfold cmp99Eq337PhysicalComplexPerturbedLinkRadius
    have hbudget : 0 ≤ cmp99SUNLieComplexCoordMatrixNormBudget Nc :=
      cmp99SUNLieComplexCoordMatrixNormBudget_nonneg
    simp only [abs_zero, zero_mul, mul_zero, add_zero]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (abs_nonneg eta) hbudget) hrA))
  have hbase : ∀ e,
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
    intro e
    exact (hbase0 e).trans hradius_mono
  have hpert : ∀ e,
      ‖(background1 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
    intro e
    simpa [background1] using
      norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
        U A eta epsilonU rA hA hsmall hU e
  exact cmp99Eq359ComplexClosedPhysicalTowerPairAux
    (d := d) (M := M) (Nc := Nc) (depth := depth)
    hd hM (cmp99Eq337PhysicalComplexPerturbedLinkRadius
      Nc epsilonU eta rA) R B regions spacing 0 (by omega)
    background0 background1 hbase hpert

end

end YangMills.RG
