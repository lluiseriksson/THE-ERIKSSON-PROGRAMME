import tmp.BalabanCMP99Eq351ComplexRegionalLaplacianStencil.draft
import tmp.BalabanCMP99Eq351PhysicalComplexOrientedAdjointExpansion.draft
import YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51): raw two-orientation regrouping

Before cancelling any spacing factor, the perturbation of the unscaled
regional stencil is the negative sum of the canonical positive- and
negative-edge adjoint increments.  This leaf performs that exact additive
regrouping only.  The commutator sum has not yet been identified with the
printed first and diagonal species.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {d N Nc : Nat} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal sum of the two canonical oriented increments at one output site.
The target values are read from the same Dirichlet extension as the analytic
regional Laplacian. -/
def cmp99Eq351PhysicalComplexOrientedStencilIncrementMatrix
    (Omega : ActiveGaugeRegion d N)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  let extended := cmp99Eq360ComplexDirichletExtend Omega phi
  ∑ i : Fin d,
    (cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix
        U A eta (ConcreteEdge.mk x.1 i true) (extended (x.1.shift i)) +
      cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix
        U A eta (ConcreteEdge.mk (x.1.shiftBack i) i false)
        (extended (x.1.shiftBack i)))

/-- Raw all-spacing form of the source regrouping at the unscaled-stencil
level.  No inverse-spacing factor has been cancelled and no nonzero premise
is needed. -/
theorem cmp99Eq351ComplexOrientedLaplacianStencil_regrouping_raw
    (Omega : ActiveGaugeRegion d N)
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99Eq351ComplexRegionalOrientedLaplacianStencil Omega
          (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) phi x) =
      cmp99SUNLieComplexCoordMatrixLM Nc
          (cmp99Eq351ComplexRegionalOrientedLaplacianStencil Omega
            (cmp99PhysicalGaugeBackgroundToSpecialLinear U) phi x) -
        cmp99Eq351PhysicalComplexOrientedStencilIncrementMatrix
          Omega U A eta phi x := by
  simp only [cmp99Eq351ComplexRegionalOrientedLaplacianStencil,
    cmp99Eq351PhysicalComplexOrientedStencilIncrementMatrix,
    map_sum, map_add, map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  have hpos :=
    cmp99Eq351PhysicalComplexOrientedAdjoint_sub_baseline_eq_increment
      U A eta (ConcreteEdge.mk x.1 i true)
        (cmp99Eq360ComplexDirichletExtend Omega phi (x.1.shift i))
  have hneg :=
    cmp99Eq351PhysicalComplexOrientedAdjoint_sub_baseline_eq_increment
      U A eta (ConcreteEdge.mk (x.1.shiftBack i) i false)
        (cmp99Eq360ComplexDirichletExtend Omega phi (x.1.shiftBack i))
  simp only [cmp99PhysicalGaugeBackgroundToSpecialLinear_apply]
  module

end

end YangMills.RG
