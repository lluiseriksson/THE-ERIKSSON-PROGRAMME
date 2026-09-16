import YangMills.RG.BalabanCMP116WilsonHessianEnergyOverlap
import YangMills.RG.PhysicalCoerciveCombesThomas
import YangMills.RG.PhysicalBondDistance

/-!
# Weighted Schur bounds for the interacting Wilson Hessian defect

This module combines three already physical facts:

* the defect has exact physical-bond range two;
* its entrywise norm is bounded uniformly in the volume;
* physical bond balls have an explicit volume-independent cardinality bound.

It instantiates the repository's weighted-conjugation Schur machinery and
produces explicit bounds for both the tilted defect and the tilt
perturbation.  No coercivity claim is made here: the complete interacting
precision may also contain background-dependent gauge-fixing terms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The explicit unweighted Wilson-defect coefficient. -/
def cmp116WilsonHessianDefectRate (d Nc : ℕ) (ε : ℝ) : ℝ :=
  ((256 * Nc * d : ℕ) : ℝ) * ε

/-- The explicit physical-bond ball budget at the exact defect range two. -/
def cmp116WilsonHessianRangeTwoBallBudget (d : ℕ) : ℕ :=
  (2 * (2 + 1)) ^ d * d

theorem cmp116WilsonHessianDefectRate_nonneg
    (ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ cmp116WilsonHessianDefectRate d Nc ε := by
  unfold cmp116WilsonHessianDefectRate
  positivity

/-- Weighted entrywise bound for the conjugated Wilson defect. -/
theorem physicalWilsonHessianDefect_tilt_kernelBound
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (μ : ℝ) (hμ : 0 ≤ μ) (root : PhysicalBond d N) :
    PhysicalCovarianceKernelBound
      (physicalTiltConjCLM (Nc := Nc) physicalBondDist μ root
        (physicalWilsonHessianDefectCLM U))
      (fun _target _source =>
        cmp116WilsonHessianDefectRate d Nc ε *
          Real.exp (μ * (2 : ℝ))) := by
  exact physicalTiltConjCLM_kernelBound
    physicalBondDist physicalBondDist_comm physicalBondDist_triangle
    hμ root (cmp116WilsonHessianDefectRate_nonneg ε hε)
    (physicalWilsonHessianDefectCLM_finiteRange U)
    (by
      simpa [cmp116WilsonHessianDefectRate] using
        physicalWilsonHessianDefectCLM_kernelBound U ε hε hsmall)

/-- Weighted Schur bound for the conjugated Wilson defect.  Every constant is
independent of the periodic volume `N`. -/
theorem norm_physicalWilsonHessianDefect_tilt_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (μ : ℝ) (hμ : 0 ≤ μ) (root : PhysicalBond d N) :
    ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist μ root
        (physicalWilsonHessianDefectCLM U)‖ ≤
      cmp116WilsonHessianDefectRate d Nc ε *
        Real.exp (μ * (2 : ℝ)) *
        (cmp116WilsonHessianRangeTwoBallBudget d : ℝ) := by
  apply physicalOpNorm_le_of_kernelBound_finiteRange
    physicalBondDist physicalBondDist_comm
  · have hrate := cmp116WilsonHessianDefectRate_nonneg
      (d := d) (Nc := Nc) ε hε
    positivity
  · intro x
    exact physicalBondDist_ball_card_le x 2
  · exact physicalTiltConjCLM_finiteRange physicalBondDist μ root
      (physicalWilsonHessianDefectCLM_finiteRange U)
  · exact physicalWilsonHessianDefect_tilt_kernelBound
      U ε hε hsmall μ hμ root

/-- The explicit weighted perturbation cost
`‖T_μ K T_{-μ} - K‖`.  This is the quantity later consumed by coercivity
survival, once the complete background-dependent precision is constructed. -/
theorem norm_physicalWilsonHessianDefect_tilt_sub_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (μ : ℝ) (hμ : 0 ≤ μ) (root : PhysicalBond d N) :
    ‖physicalTiltConjCLM (Nc := Nc) physicalBondDist μ root
          (physicalWilsonHessianDefectCLM U) -
        physicalWilsonHessianDefectCLM U‖ ≤
      cmp116WilsonHessianDefectRate d Nc ε *
        (Real.exp (μ * (2 : ℝ)) - 1) *
        (cmp116WilsonHessianRangeTwoBallBudget d : ℝ) := by
  exact norm_physicalTiltConj_sub_le
    physicalBondDist physicalBondDist_comm physicalBondDist_triangle
    hμ root (cmp116WilsonHessianDefectRate_nonneg ε hε)
    (fun x => physicalBondDist_ball_card_le x 2)
    (physicalWilsonHessianDefectCLM_finiteRange U)
    (by
      simpa [cmp116WilsonHessianDefectRate] using
        physicalWilsonHessianDefectCLM_kernelBound U ε hε hsmall)

end

end YangMills.RG
