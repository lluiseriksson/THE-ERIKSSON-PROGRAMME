import tmp.BalabanCMP99Eq360ComplexRegionalLaplacian.draft
import YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointComposition

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51): the two-orientation regional stencil

The analytic regional Laplacian is first reduced to its literal unscaled
nearest-neighbour stencil.  A second theorem identifies the incoming term
with the canonical negative concrete edge.  Both equalities hold for every
spacing, including zero; no `eta⁻¹ * eta` cancellation occurs in this leaf.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Unscaled complex Dirichlet stencil underlying the regional analytic
covariant Laplacian.  Its incoming link is still written as the inverse of
the positive bond, exactly as in the definition of `D_U^* D_U`. -/
def cmp99Eq351ComplexRegionalLaplacianStencil
    (Omega : ActiveGaugeRegion d N)
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) : SUNLieComplexCoord Nc :=
  let extended := cmp99Eq360ComplexDirichletExtend Omega phi
  ∑ i : Fin d,
    ((extended x.1 -
        cmp99SpecialLinearAdjointCoordLM
          (U (positiveEdgeOfPhysicalBond ((x.1, i) : PhysicalBond d N)))
          (extended (x.1.shift i))) -
      (cmp99SpecialLinearAdjointCoordLM
          (U (positiveEdgeOfPhysicalBond
            ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
          (extended (x.1.shiftBack i)) - extended x.1))

/-- The analytic regional Laplacian is exactly two explicit inverse-spacing
factors times the unscaled stencil.  This is an all-spacing identity, not the
printed nonzero-spacing simplification. -/
theorem cmp99Eq360ComplexRegionalLaplacian_apply_eq_stencil
    (Omega : ActiveGaugeRegion d N)
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (eta : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99Eq360ComplexRegionalLaplacian Omega U eta phi x =
      ((eta : ℂ)⁻¹) • ((eta : ℂ)⁻¹) •
        cmp99Eq351ComplexRegionalLaplacianStencil Omega U phi x := by
  rw [cmp99Eq360ComplexRegionalLaplacian_apply]
  simp only [cmp99Eq360ComplexCovariantDifference, map_smul, map_sub,
    cmp99SpecialLinearAdjointCoordLM_inv_apply,
    FinBox.shift_shiftBack]
  simp only [cmp99Eq351ComplexRegionalLaplacianStencil,
    Finset.smul_sum, smul_sub]

/-- The same unscaled stencil written as a sum over the two canonical
concrete edges leaving `x`.  The incoming edge is the negative edge stored at
`x.shiftBack i`; its equality with the inverse positive link is derived from
`GaugeConfig.map_reverse`, not assumed as an orientation convention. -/
def cmp99Eq351ComplexRegionalOrientedLaplacianStencil
    (Omega : ActiveGaugeRegion d N)
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) : SUNLieComplexCoord Nc :=
  let extended := cmp99Eq360ComplexDirichletExtend Omega phi
  ∑ i : Fin d,
    ((extended x.1 -
        cmp99SpecialLinearAdjointCoordLM
          (U (ConcreteEdge.mk x.1 i true)) (extended (x.1.shift i))) +
      (extended x.1 -
        cmp99SpecialLinearAdjointCoordLM
          (U (ConcreteEdge.mk (x.1.shiftBack i) i false))
          (extended (x.1.shiftBack i))))

/-- The inverse-positive and canonical-negative presentations of the stencil
agree exactly. -/
theorem cmp99Eq351ComplexRegionalLaplacianStencil_eq_oriented
    (Omega : ActiveGaugeRegion d N)
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99Eq351ComplexRegionalLaplacianStencil Omega U phi x =
      cmp99Eq351ComplexRegionalOrientedLaplacianStencil Omega U phi x := by
  simp only [cmp99Eq351ComplexRegionalLaplacianStencil,
    cmp99Eq351ComplexRegionalOrientedLaplacianStencil,
    positiveEdgeOfPhysicalBond]
  apply Finset.sum_congr rfl
  intro i _hi
  have hreverse := U.map_reverse
    (ConcreteEdge.mk (x.1.shiftBack i) i true)
  change U (ConcreteEdge.mk (x.1.shiftBack i) i false) =
      (U (ConcreteEdge.mk (x.1.shiftBack i) i true))⁻¹ at hreverse
  rw [hreverse]
  module

end

end YangMills.RG
