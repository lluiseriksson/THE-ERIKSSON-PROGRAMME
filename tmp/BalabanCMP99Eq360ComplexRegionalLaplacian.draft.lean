import tmp.BalabanCMP99ComplexSpecialLinearAdjointAction.draft
import YangMills.RG.PhysicalGaugeOperator

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51)--(3.54): analytic regional covariant Laplacian

The analytically continued background is `SL(N,C)`-valued, so the physical
Hilbert adjoint cannot be reused away from the compact real slice.  This leaf
constructs the Dirichlet stencil directly: the forward difference uses
algebraic conjugation and the backward term uses the inverse group element.
The lattice-spacing factors and zero extension are literal.

This is the operator needed to stop passing the two Laplacians of (3.60) as
free data.  The compact-real-slice comparison and the local expansion into
the printed `V'_1(A)` remain separate obligations; neither is asserted here.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Dirichlet zero extension in the complex Lie-coordinate fibre. -/
noncomputable def cmp99Eq360ComplexDirichletExtend
    (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc)) :
    GaugeZeroCochain d N (SUNLieComplexCoord Nc) :=
  WithLp.toLp 2 fun x =>
    if hx : x ∈ Omega.sites then phi ⟨x, hx⟩ else 0

theorem cmp99Eq360ComplexDirichletExtend_add
    (Omega : ActiveGaugeRegion d N)
    (phi psi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc)) :
    cmp99Eq360ComplexDirichletExtend Omega (phi + psi) =
      cmp99Eq360ComplexDirichletExtend Omega phi +
        cmp99Eq360ComplexDirichletExtend Omega psi := by
  ext x
  by_cases hx : x ∈ Omega.sites <;>
    simp [cmp99Eq360ComplexDirichletExtend, hx]

theorem cmp99Eq360ComplexDirichletExtend_smul
    (Omega : ActiveGaugeRegion d N) (c : ℂ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc)) :
    cmp99Eq360ComplexDirichletExtend Omega (c • phi) =
      c • cmp99Eq360ComplexDirichletExtend Omega phi := by
  ext x
  by_cases hx : x ∈ Omega.sites <;>
    simp [cmp99Eq360ComplexDirichletExtend, hx]

/-- One scaled forward covariant difference for an analytic background. -/
def cmp99Eq360ComplexCovariantDifference
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (b : PhysicalBond d N) : SUNLieComplexCoord Nc :=
  ((spacing : ℂ)⁻¹) •
    (phi b.1 -
      cmp99SpecialLinearAdjointCoordLM
        (U (positiveEdgeOfPhysicalBond b)) (phi (b.1.shift b.2)))

theorem cmp99Eq360ComplexCovariantDifference_add
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ)
    (phi psi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (b : PhysicalBond d N) :
    cmp99Eq360ComplexCovariantDifference U spacing (phi + psi) b =
      cmp99Eq360ComplexCovariantDifference U spacing phi b +
        cmp99Eq360ComplexCovariantDifference U spacing psi b := by
  simp [cmp99Eq360ComplexCovariantDifference, smul_sub, smul_add]

theorem cmp99Eq360ComplexCovariantDifference_smul
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ) (c : ℂ)
    (phi : GaugeZeroCochain d N (SUNLieComplexCoord Nc))
    (b : PhysicalBond d N) :
    cmp99Eq360ComplexCovariantDifference U spacing (c • phi) b =
      c • cmp99Eq360ComplexCovariantDifference U spacing phi b := by
  simp [cmp99Eq360ComplexCovariantDifference, smul_sub, smul_smul]
  module

/-- Literal analytic Dirichlet covariant Laplacian on one active carrier.

The backward factor is algebraic conjugation by the inverse `SL(N,C)` link.
No `ContinuousLinearMap.adjoint` occurs in this definition. -/
noncomputable def cmp99Eq360ComplexRegionalLaplacian
    (Omega : ActiveGaugeRegion d N)
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi =>
        let extended := cmp99Eq360ComplexDirichletExtend Omega phi
        WithLp.toLp 2 fun x =>
          ((spacing : ℂ)⁻¹) •
            ∑ i : Fin d,
              (cmp99Eq360ComplexCovariantDifference U spacing extended
                  (x.1, i) -
                cmp99SpecialLinearAdjointCoordLM
                  (U (positiveEdgeOfPhysicalBond
                    ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
                  (cmp99Eq360ComplexCovariantDifference U spacing extended
                    (x.1.shiftBack i, i)))
      map_add' := fun phi psi => by
        ext x
        simp only [cmp99Eq360ComplexDirichletExtend_add,
          cmp99Eq360ComplexCovariantDifference_add, map_add,
          Finset.sum_add_distrib, smul_add, PiLp.add_apply]
        module
      map_smul' := fun c phi => by
        ext x
        simp only [cmp99Eq360ComplexDirichletExtend_smul,
          cmp99Eq360ComplexCovariantDifference_smul, map_smul,
          Finset.smul_sum, smul_sub, smul_smul, PiLp.smul_apply]
        module }

@[simp] theorem cmp99Eq360ComplexRegionalLaplacian_apply
    (Omega : ActiveGaugeRegion d N)
    (U : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99Eq360ComplexRegionalLaplacian Omega U spacing phi x =
      let extended := cmp99Eq360ComplexDirichletExtend Omega phi
      ((spacing : ℂ)⁻¹) •
        ∑ i : Fin d,
          (cmp99Eq360ComplexCovariantDifference U spacing extended (x.1, i) -
            cmp99SpecialLinearAdjointCoordLM
              (U (positiveEdgeOfPhysicalBond
                ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
              (cmp99Eq360ComplexCovariantDifference U spacing extended
                (x.1.shiftBack i, i))) :=
  rfl

end

end YangMills.RG
