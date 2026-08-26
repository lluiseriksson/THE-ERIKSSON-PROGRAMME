import YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusPhysicalGates
import YangMills.RG.BalabanCMP99SourceRegionalLiftTower

/-!
PRE-VALIDATION: scratch closed physical recursion. This file has no
materialized `.olean` and no compiler or axiom-oracle verdict.

The public constructor starts from the literal Eq. (3.37) `U`, `A` and
`eta`. A private recursion constructs every coarse background internally and
returns the terminal background with its generated all-orientation radius.
No background family, radius family, deviation family or per-scale gate is
caller data.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable [NeZero (d * (M - 1))]

/-- Terminal output of the private recursion, retaining only the final
background and its generated radius theorem. -/
private structure CMP99Eq337ComplexClosedRecursiveAuxResult
    (L M k remaining : ℕ) (r0 : ℝ) where
  background : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ)
  bound : ∀ e,
    ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99ComplexClosedRadiusAt L M r0 (k + remaining)

/-- Private fine-to-coarse recursion. The index `k` records the number of
already generated source steps, while `remaining` is the literal lattice
depth still to be coarsened. -/
private noncomputable def cmp99Eq337ComplexClosedRecursiveAux
    (hd : 2 ≤ d) (hM : 2 ≤ M) (r0 R : ℝ)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth r0 R (cmp99UbarNoWindingThreshold Nc)) :
    ∀ (remaining k : ℕ), k + remaining ≤ depth →
      (background : GaugeConfig d
        (cmp99RegionalLatticeSize M N remaining)
        (Matrix.SpecialLinearGroup (Fin Nc) ℂ)) →
      (∀ e,
        ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 k) →
      CMP99Eq337ComplexClosedRecursiveAuxResult
        (d := d) (N := N) (Nc := Nc)
        (d * (M - 1)) M k remaining r0 := by
  intro remaining
  induction remaining with
  | zero =>
      intro k hdepth background hlink
      exact {
        background := by simpa using background
        bound := by
          intro e
          simpa using hlink e }
  | succ remaining ih =>
      intro k hdepth background hlink
      letI : NeZero (cmp99RegionalLatticeSize M N remaining) := inferInstance
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
      let nextBackground : GaugeConfig d
          (cmp99RegionalLatticeSize M N remaining)
          (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
        cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius
          (d := d) (M := M)
          (N' := cmp99RegionalLatticeSize M N remaining) (Nc := Nc)
          hd hM background r hr hlink hnoWinding
      have hnext : ∀ e,
          ‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
            cmp99ComplexClosedRadiusAt (d * (M - 1)) M r0 (k + 1) := by
        intro e
        have hphysical :=
          norm_cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius_sub_one_le
            (d := d) (M := M)
            (N' := cmp99RegionalLatticeSize M N remaining) (Nc := Nc)
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
      let tail := ih (k + 1) (by omega) nextBackground hnext
      exact {
        background := tail.background
        bound := by
          intro e
          simpa [Nat.add_assoc] using tail.bound e }

/-- Literal closed Eq. (3.37) complex recursion. The perturbed fine
background and every subsequent source background are constructed internally
from the physical input and the single initial-scale scalar budget. -/
noncomputable def cmp99Eq337SourceComplexClosedRecursiveBackground
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d
      (cmp99RegionalLatticeSize M N depth) Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d
      (cmp99RegionalLatticeSize M N depth) Nc)
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
    GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
  (cmp99Eq337ComplexClosedRecursiveAux
    (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth)
    hd hM (cmp99Eq337PhysicalComplexPerturbedLinkRadius
      Nc epsilonU eta rA) R B depth 0 (by omega)
    (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) (by
      intro e
      simpa using
        norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
          U A eta epsilonU rA hA hsmall hU e)).background

/-- The terminal background carries the exact generated all-orientation
radius at the requested depth. -/
theorem norm_cmp99Eq337SourceComplexClosedRecursiveBackground_sub_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (U : PhysicalGaugeBackground d
      (cmp99RegionalLatticeSize M N depth) Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d
      (cmp99RegionalLatticeSize M N depth) Nc)
    (eta epsilonU rA R : ℝ)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (B : CMP99ComplexClosedRadiusBudget
      (d * (M - 1)) M depth
      (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
      R (cmp99UbarNoWindingThreshold Nc))
    (e : ConcreteEdge d N) :
    ‖(cmp99Eq337SourceComplexClosedRecursiveBackground
        (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth)
        hd hM U A eta epsilonU rA R hA hsmall hU B e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99ComplexClosedRadiusAt (d * (M - 1)) M
        (cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
        depth := by
  exact (cmp99Eq337ComplexClosedRecursiveAux
    (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth)
    hd hM (cmp99Eq337PhysicalComplexPerturbedLinkRadius
      Nc epsilonU eta rA) R B depth 0 (by omega)
    (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) (by
      intro e'
      simpa using
        norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
          U A eta epsilonU rA hA hsmall hU e')).bound e

end

end YangMills.RG
