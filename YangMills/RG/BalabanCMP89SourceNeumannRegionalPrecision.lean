import YangMills.RG.BalabanCMP99SourceRetainedPhysicalPrecision

/-!
# CMP89 source-faithful regional Neumann precision

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this module is compiler-verified.

CMP89 defines its rectangular local Green with Neumann/free boundary
conditions: the covariant derivative is read only on bonds whose two
endpoints lie in the region.  This differs from the existing CMP99 regional
Dirichlet operator, which applies the ambient derivative to a zero extension
before taking its adjoint and therefore charges boundary-crossing bonds.

This module introduces only the source-faithful internal-bond operator and
its exact algebraic laws.  It does not identify the source rectangle with a
CMP96 support thickening, construct the Green, or claim the uniform bounds of
CMP89 Lemma 2.4.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The source Neumann covariant derivative: zero extension is harmless on
the internal-bond restriction, and no boundary-crossing bond is retained. -/
noncomputable def cmp89SourceNeumannRegionalCovariantD0CLM
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeOneCochain Omega (SUNLieCoord Nc) :=
  spacing⁻¹ •
    (restrictOneCLM (𝔤 := SUNLieCoord Nc) Omega).comp
      ((covariantD0CLM rho U).comp
        (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega))

/-- The internal-bond Neumann Laplacian. -/
noncomputable def cmp89SourceNeumannRegionalLaplacian
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing).adjoint.comp
    (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing)

/-- Exact Neumann energy identity. -/
theorem inner_cmp89SourceNeumannRegionalLaplacian
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    inner ℝ phi
        (cmp89SourceNeumannRegionalLaplacian Omega rho U spacing phi) =
      ‖cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi‖ ^ 2 := by
  rw [cmp89SourceNeumannRegionalLaplacian,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

/-- The source Neumann Laplacian is self-adjoint. -/
theorem cmp89SourceNeumannRegionalLaplacian_isSymmetric
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    (cmp89SourceNeumannRegionalLaplacian Omega rho U spacing).IsSymmetric := by
  let D := cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing
  intro phi psi
  change inner ℝ ((D.adjoint.comp D) phi) psi =
    inner ℝ phi ((D.adjoint.comp D) psi)
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

end

end YangMills.RG
